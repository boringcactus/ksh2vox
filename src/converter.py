#!/usr/bin/env python3.7
import argparse
from collections import defaultdict
from dataclasses import dataclass
from enum import Enum, auto
from functools import total_ordering
from glob import glob
import math
import os
from os.path import splitext as splitx
import re
import shutil
import sys
import threading
import time
import traceback
from xml.etree import ElementTree

import ksh_effects

# Ticks per a beat of /4 time
TICKS_PER_BEAT = 48

SLAM_TICKS = 4

FX_CHIP_SOUND_COUNT = 14

KSH_DEFAULT_FILTER_GAIN = 50
KSH_DEFAULT_SLAM_VOL = 40

EFFECT_FALLBACK_NAME = 'fallback'

AUDIO_EXTENSION = '.ogg'
FX_CHIP_SOUND_EXTENSION = '.wav'

FX_CHIP_SOUND_VOL_PERCENT = 27

MAX_MEASURES = 999

def to_path(text):
    return re.sub(r'[^\w]+', '_', text)

class Debug:
    class State(Enum):
        INPUT = auto()
        OUTPUT = auto()

    class Level(Enum):
        ABNORMALITY = 'abnormal'
        WARNING = 'warning'
        ERROR = 'error'

    def __init__(self, exceptions_file):
        self.state = None
        self.input_filename = None
        self.output_filename = None
        self.current_line_num = 0
        self.exceptions_count = {level: 0 for level in Debug.Level}
        self.exceptions_file = open(exceptions_file, 'w+')

    def reset(self):
        for level in self.Level:
            self.exceptions_count[level] = 0

    def close(self):
        self.exceptions_file.close()

    def current_filename(self):
        return self.input_filename if self.state == self.State.INPUT else self.output_filename

    def record(self, level, tag, message):
        self.exceptions_count[level] += 1
        print(f'{self.current_filename()}:{self.current_line_num}\n{level.value} / {tag}: {message}\n',
              file=self.exceptions_file)

    def has_issues(self):
        for level in self.Level:
            if self.exceptions_count[level] > 0:
                return True
        return False

    def record_last_exception(self, level=Level.WARNING, tag='python_exception', trace=False):
        self.record(level, tag, str(sys.exc_info()[1]) + '\n\tTraceback:\n' + '\n'.join(traceback.format_tb(sys.exc_info()[2])))

def truncate(x, digits) -> float:
    stepper = 10.0 ** digits
    return math.trunc(stepper * x) / stepper

class KshLoadError(Exception):
    pass

class KshParseError(Exception):
    pass

class VoxConvertError(Exception):
    pass

class TimeSignature:
    def __init__(self, top, bottom):
        self.top: int = top
        self.bottom: int = bottom

    def ticks_per_beat(self):
        return int(TICKS_PER_BEAT * (4 / self.bottom))

class Timing:
    # TODO Take timesig as a param
    def __init__(self, measure, beat, offset):
        self.measure: int = measure
        self.beat: int = beat
        self.offset: int = offset

    def to_time_str(self):
        """ Create the format string that appears in the first column of vox tracks. """
        return '{:03},{:02},{:02}'.format(self.measure, self.beat, self.offset)

    def diff(self, other, timesig):
        return (self.measure - other.measure) * (timesig.ticks_per_beat() * timesig.top) \
               + (self.beat - other.beat) * timesig.ticks_per_beat() \
               + (self.offset - other.offset)

    def add(self, ticks, timesig):
        new = Timing(self.measure, self.beat, self.offset + ticks)
        while new.offset >= timesig.ticks_per_beat():
            new.offset -= timesig.ticks_per_beat()
            new.beat += 1
        while new.beat > timesig.top:
            new.beat -= timesig.top
            new.measure += 1
        return new

    def __eq__(self, other):
        return self.measure == other.measure and self.beat == other.beat and self.offset == other.offset

    def __hash__(self):
        return hash((self.measure, self.beat, self.offset))

    def __str__(self):
        return '{},{},{}'.format(self.measure, self.beat, self.offset)

    def __lt__(self, other):
        return (self.measure, self.beat, self.offset) < (other.measure, other.beat, other.offset)

@dataclass()
class CameraNode:
    start_param: float
    end_param: float
    duration: int

# TODO Use mapped_enum
class SpcParam(Enum):
    """ SPCONTROLLER section param. """
    def to_vox_name(self):
        if self == self.ROT_X:
            return 'CAM_RotX'
        elif self == self.RAD_I:
            return 'CAM_Radi'
        elif self == self.REALIZE:
            return 'Realize'
        elif self == self.AIRL_SCAX:
            return 'AIRL_ScaX'
        elif self == self.AIRR_SCAX:
            return 'AIRR_ScaX'
        elif self == self.TILT:
            return 'Tilt'
        elif self == self.LANE_Y:
            return 'LaneY'
        else:
            return None

    def is_state(self):
        return self == self.LANE_Y

    @classmethod
    def from_ksh_name(cls, ksh_name):
        if ksh_name == 'zoom_top':
            return cls.ROT_X
        elif ksh_name == 'zoom_bottom':
            return cls.RAD_I
        elif ksh_name == 'tilt':
            return cls.TILT
        elif ksh_name == 'lane_toggle':
            return cls.LANE_Y
        else:
            return None

    def from_ksh_value(self, val:float=0):
        # Convert the ksh value to the one that will be printed to the vox.
        if self == self.ROT_X:
            return val / 150.0
        elif self == self.RAD_I:
            return val / -150.0
        elif self == self.TILT:
            return -val
        elif self == self.LANE_Y:
            return float(val)
        return None

    ROT_X = auto()
    RAD_I = auto()
    REALIZE = auto()
    AIRL_SCAX = auto()
    AIRR_SCAX = auto()
    TILT = auto()
    LANE_Y = auto()

    @classmethod
    def line_is_abnormal(cls, param, splitted):
        cell = lambda i: splitted[i].strip()
        if param == SpcParam.REALIZE:
            if cell(2) == '3':
                return cell(4) != '36.12' or cell(5) != '60.12' or cell(6) != '110.12' or cell(7) != '0.00'
            elif cell(2) == '4':
                return cell(4) != '0.62' or cell(5) != '0.72' or cell(6) != '1.03' or cell(7) != '0.00'
        return False
        # TODO Other params maybe

class KshFilter(Enum):
    def to_vox_filter_id(self):
        # TODO Correct this so filter indices line up with the TAB EFFECT INFO instead of being hardcoded
        if self == self.PEAK:
            return 0
        elif self == self.LOWPASS:
            return 1 # or 2
        elif self == self.HIGHPASS:
            return 3 # or 4
        elif self == self.BITCRUSH:
            return 5
        elif self == self.PEAK:
            # TODO Figure out how effect 6 (and up?) is assigned.
            return 6
        raise ValueError(f'unrecognized vox filter id {self}')

    @classmethod
    def from_ksh_name(cls, ksh_name):
        if ksh_name == 'peak':
            return cls.PEAK
        elif ksh_name == 'lpf1':
            return cls.LOWPASS
        elif ksh_name == 'hpf1':
            return cls.HIGHPASS
        elif ksh_name == 'bitc':
            return cls.BITCRUSH

    PEAK = auto()
    LOWPASS = auto()
    HIGHPASS = auto()
    BITCRUSH = auto()

# TODO what uhhhhh the fuck is any of this
class KshEffectDefine:
    def __init__(self):
        self.effect = None
        self.main_param = None
        self.params = {}

    def define_line(self, index):
        param_str = ''
        for k, v in self.params.items():
            param_str += f';{k}={v}'
        return f'#define_fx {index} type={self.effect.to_ksh_simple_name()}{param_str}'

    def fx_change(self, index, duration=0):
        if self.effect == ksh_effects.KshEffectKind.TAPESTOP:
            # Math lol
            extra = f';{int(2500 / (duration + 10))}'
        else:
            extra = f';{self.main_param}' if self.main_param is not None else ''
        return f'{index}{extra}'

    @classmethod
    def from_pre_v4_vox_sound_id(cls, sound_id):
        """Generate an effect definition line from the old-style effect declaration."""
        effect = None
        main_param = None

        from ksh_effects import KshEffectKind as Kind

        if sound_id == 2:
            effect = Kind.RETRIGGER
            main_param = '8'
        elif sound_id == 3:
            effect = Kind.RETRIGGER
            main_param = '16'
        elif sound_id == 4:
            effect = Kind.GATE
            main_param = '16'
        elif sound_id == 5:
            effect = Kind.FLANGER
            main_param = '200'
        elif sound_id == 6:
            effect = Kind.RETRIGGER
            main_param = '32'
        elif sound_id == 7:
            effect = Kind.GATE
            main_param = '8'
        elif sound_id == 8:
            effect = Kind.PITCHSHIFT
            main_param = '8' # TODO Tweak
        elif sound_id > 8:
            debug().record(Debug.Level.WARNING, 'fx_parse', f'old vox sound id {sound_id} unknown')

        return ksh_effects.KshEffect(effect, main_param=main_param) \
            if effect is not None and main_param is not None \
            else cls.default_effect()

    @classmethod
    def default_effect(cls):
        define = ksh_effects.KshEffect(ksh_effects.KshEffectKind.FLANGER, main_param='200')
        define.params['depth'] = f'{define.main_param}samples'
        return define

    @classmethod
    def from_effect_info_line(cls, line):
        splitted = line.replace('\t', '').split(',')

        if splitted[0] == '1':
            return ksh_effects.RetriggerEffect(*splitted[1:])
        elif splitted[0] == '2':
            return ksh_effects.GateEffect(*splitted[1:])
        elif splitted[0] == '3':
            return ksh_effects.PhaserEffect(*splitted[1:])
        elif splitted[0] == '4':
            return ksh_effects.TapestopEffect(*splitted[1:])
        elif splitted[0] == '5':
            return ksh_effects.SidechainEffect(*splitted[1:])
        elif splitted[0] == '6':
            return ksh_effects.WobbleEffect(*splitted[1:])
        elif splitted[0] == '7':
            return ksh_effects.BitcrusherEffect(*splitted[1:])
        elif splitted[0] == '8':
            return ksh_effects.UpdateableRetriggerEffect(*splitted[1:])
        elif splitted[0] == '9':
            return ksh_effects.PitchshiftEffect(*splitted[1:])
        elif splitted[0] == '11':
            return ksh_effects.LowpassEffect(*splitted[1:])
        elif splitted[0] == '12':
            return ksh_effects.FlangerEffect(*splitted[1:])
        else:
            raise ValueError(f'effect define id {splitted[0]} is not supported')

class TabEffectInfo:
    # TODO This is a placeholder
    @staticmethod
    def line_is_abnormal(line_num, line):
        line = line.strip()
        if line_num == 1:
            return line != '1,	90.00,	400.00,	18000.00,	0.70'
        elif line_num == 2:
            return line != '1,	90.00,	600.00,	15000.00,	5.00'
        elif line_num == 3:
            return line != '2,	90.00,	40.00,	5000.00,	0.70'
        elif line_num == 4:
            return line != '2,	90.00,	40.00,	2000.00,	3.00'
        elif line_num == 5:
            return line != '3,	100.00,	30'
        raise ValueError(f'invalid line number {line_num}')

class TabParamAssignInfo:
    # TODO This is a placeholder.
    @staticmethod
    def line_is_abnormal(line):
        return not line.endswith('0,	0.00,	0.00')

class Button(Enum):
    def is_fx(self):
        return self == Button.FX_L or self == Button.FX_R

    @classmethod
    def from_track_num(cls, num: int):
        try:
            return next(x for x in cls if x.value == num)
        except StopIteration as err:
            if num != 9:
                raise ValueError(f'invalid track number for button: {num}') from err

    def to_track_num(self):
        return self.value

    BT_A = 3
    BT_B = 4
    BT_C = 5
    BT_D = 6
    FX_L = 2
    FX_R = 7

@dataclass()
class ButtonPress:
    button: Button
    duration: int
    effect: int

class LaserSide(Enum):
    LEFT = 'l', 1
    RIGHT = 'r', 8

    def to_letter(self):
        return self.value[0]

    def to_track_num(self):
        return self.value[1]

class LaserCont(Enum):
    """ The continuity status of a laser node. """
    CONTINUE = 0
    START = 1
    END = 2

class RollKind(Enum):
    MEASURE = 1
    HALF_MEASURE = 2
    THREE_BEAT = 3
    CANCER = 4
    SWING = 5

class LaserNode:
    @dataclass()
    class Builder:
        side: LaserSide = None
        position: int = None
        node_type: LaserCont = None
        range: int = 1
        filter: KshFilter = KshFilter.PEAK
        roll_kind: RollKind = None

    def __init__(self, builder: Builder):
        self.side: LaserSide = builder.side
        self.position: int = builder.position
        self.node_cont: LaserCont = builder.node_type
        self.range: int = builder.range
        self.filter: KshFilter = builder.filter
        self.roll_kind: RollKind = builder.roll_kind

        if self.position < 0 or self.position > 127:
            raise ValueError(f'position {self.position} is out of bounds')

    @staticmethod
    def position_ksh(position):
        """ Convert the position from whatever the hell KSM is using to the 7-bit scale. """
        chars = []
        for char in range(10):
            chars.append(chr(ord('0') + char))
        for char in range(24):
            chars.append(chr(ord('A') + char))
        for char in range(15):
            chars.append(chr(ord('a') + char))
        idx = chars.index(position)
        return (idx / (len(chars) - 1)) * 127

class LaserSlam:
    class Direction(Enum):
        LEFT = auto()
        RIGHT = auto()

    def __init__(self, start: LaserNode, end: LaserNode):
        self.start: LaserNode = start
        self.end: LaserNode = end

        if self.start.position == self.end.position:
            raise ValueError('attempt to create a slam with the same start and end')
        elif self.start.side != self.end.side:
            raise ValueError('attempt to create a slam with start and end having different sides')

    def direction(self):
        if self.start.position > self.end.position:
            return self.Direction.LEFT
        else:
            return self.Direction.RIGHT

    def side(self):
        return self.start.side

class Difficulty(Enum):
    NOVICE = 0, 'n', 'novice', 'nov'
    ADVANCED = 1, 'a', 'challenge', 'adv'
    EXHAUST = 2, 'e', 'extended', 'exh'
    INFINITE = 3, 'i', 'infinite', 'inf'
    MAXIMUM = 4, 'm', 'infinite', 'mxm'

    @classmethod
    def from_letter(cls, k):
        return next(x for x in cls if x.value[1] == k)

    def to_letter(self):
        return self.value[1]

    @classmethod
    def from_number(cls, num):
        try:
            return next(x for x in cls if x.value[0] == num)
        except StopIteration:
            # TODO Error handling.
            return None

    @classmethod
    def from_ksh_name(cls, k):
        return next(x for x in cls if x.value[2] == k)

    def to_ksh_name(self):
        return self.value[2]

    def to_xml_name(self):
        return self.name.lower()

    def to_jacket_ifs_numer(self):
        return self.value[0] + 1

    def to_abbreviation(self):
        return self.value[3]

class InfiniteVersion(Enum):
    INFINITE = 2, 'inf'
    GRAVITY = 3, 'grv'
    HEAVENLY = 4, 'hvn'
    VIVID = 5, 'vvd'

    @classmethod
    def from_inf_ver(cls, num):
        try:
            return next(x for x in cls if x.value[0] == num)
        except StopIteration:
            return None

    def to_abbreviation(self):
        return self.value[1]

class TiltMode(Enum):
    NORMAL = auto()
    BIGGER = auto()
    KEEP_BIGGER = auto()

    def to_vox_id(self):
        if self == self.NORMAL:
            return 0
        elif self == self.BIGGER:
            return 1
        elif self == self.KEEP_BIGGER:
            return 2

    @classmethod
    def from_ksh_name(cls, ksh_name):
        if ksh_name == 'normal':
            return cls.NORMAL
        elif ksh_name == 'bigger':
            return cls.BIGGER
        elif ksh_name == 'keep_bigger':
            return cls.KEEP_BIGGER

class StopEvent:
    moment: Timing
    timesig: TimeSignature

class EventKind(Enum):
    TRACK = auto()
    TIMESIG = auto()
    BPM = auto()
    TILTMODE = auto()
    SPCONTROLLER = auto()
    STOP = auto()

class Background:
    # As of 2020-01-12, using the definitions from Lasergame.
    @staticmethod
    def to_vox_id(ksh_id):
        if ksh_id == 'techno':
            return 0 # or 1, or 14..16, or 71
        elif ksh_id == 'wave':
            return 2 # or 6, or 11..13
        elif ksh_id == 'arrow':
            return 3 # or 7
        elif ksh_id == 'sakura':
            # TODO It should've been kinda a pink version of 'wave'
            return 4 # or 8
        elif ksh_id == 'smoke':
            return 63
        elif ksh_id == 'snow':
            return 65

class KshLine:
    """ Represents a single line of notes in KSH (along with effect assignment lines) """
    class ButtonState(Enum):
        NONE = auto()
        PRESS = auto()
        HOLD = auto()

    def __init__(self, line):
        buttons, fx, lasers_and_spin = line.split('|')

        self.buttons = {}
        for bt, state in zip([ Button.BT_A, Button.BT_B, Button.BT_C, Button.BT_D ], buttons):
            if state == '2':
                self.buttons[bt] = self.ButtonState.HOLD
            elif state == '1':
                self.buttons[bt] = self.ButtonState.PRESS
            else:
                self.buttons[bt] = self.ButtonState.NONE

        for bt, state in zip([ Button.FX_L, Button.FX_R ], fx):
            if state == '2':
                self.buttons[bt] = self.ButtonState.HOLD
            elif state == '1':
                self.buttons[bt] = self.ButtonState.PRESS
            else:
                self.buttons[bt] = self.ButtonState.NONE

        lasers = lasers_and_spin[:2]
        spin = lasers_and_spin[2:]

        self.lasers = {}
        for laser, state in zip([ LaserSide.LEFT, LaserSide.RIGHT ], lasers):
            self.lasers[laser] = state

        self.spin = spin

class Ksh:
    def __init__(self):
        self.kshfile = None
        self.source_file_name = None
        self.vox_defines = {} # defined in the vox file
        self.ksh_defines = {} # will be defined in the ksh file
        self.effect_fallback = KshEffectDefine.default_effect()
        self.events = defaultdict(dict)

        self.stop_point = None

        self.metadata = dict()

        self.finalized = False

        self.required_chip_sounds = set()

    def diff(self):
        return Difficulty.from_ksh_name(self.metadata['difficulty'])

    @classmethod
    def from_file(cls, path):
        global args

        parser = Ksh()

        file = open(path, 'r')
        parser.kshfile = file
        parser.source_file_name = os.path.split(path)[-1]

        return parser

    def parse(self):
        line_no = 0
        is_metadata = True
        now = Timing(0, 1, 0)
        timesig = TimeSignature(4, 4)
        for line in self.kshfile:
            line_no += 1
            debug().current_line_num = line_no

            line = line.strip().lstrip('\ufeff') # fucking BOM

            if line.startswith('//'):
                continue

            if line == '--' and is_metadata:
                is_metadata = False

            if is_metadata:
                key, value = line.split('=', 1)
                self.metadata[key] = value
                continue

            if line == '--':
                now = Timing(now.measure + 1, 1, 0)
            elif line.startswith('beat='):
                _, sig = line.split('=')
                top, bottom = sig.split('/')
                timesig = TimeSignature(int(top), int(bottom))
                self.events[now][EventKind.TIMESIG] = timesig
            elif line.startswith('t='):
                _, val = line.split('=')
                self.events[now][EventKind.BPM] = float(val)
            elif line.startswith('stop='):
                _, stop = line.split('=')
                self.events[now][EventKind.STOP] = int(stop)
            elif line.startswith('tilt='):
                _, tilt = line.split('=')
                self.events[now][EventKind.TILTMODE] = TiltMode.from_ksh_name(tilt)
            #elif SpcParam.from_ksh_name(line.split('=')[0]) is not None:
            #    raise NotImplementedError('SP Controller things are over my head')
            elif '=' in line:
                raise KshParseError('what even is a ' + line)
            else:
                ksh_line = KshLine(line)
                slam = False
                roll_kind = None
                direction = None
                if ksh_line.spin != '':
                    slam = True
                    roll_kind_code = ksh_line.spin[1]
                    if roll_kind_code in '()':
                        roll_kind = RollKind.MEASURE # or something
                        if roll_kind_code == '(':
                            direction = LaserSlam.Direction.LEFT
                        else:
                            direction = LaserSlam.Direction.RIGHT
                    elif roll_kind_code in '<>':
                        roll_kind = RollKind.SWING
                        if roll_kind_code == '<':
                            direction = LaserSlam.Direction.LEFT
                        else:
                            direction = LaserSlam.Direction.RIGHT
                for side in LaserSide:
                    if ksh_line.lasers[side] not in '-:': # TODO figure out what to do about :
                        track = side.to_track_num()
                        laser = LaserNode.Builder()
                        laser.side = side
                        laser.position = LaserNode.position_ksh(ksh_line.lasers[side])
                        laser.node_type = LaserCont.START
                        if slam:
                            laser.roll_kind = roll_kind
                            laser_start = LaserNode(laser)
                            laser.position += -1 if direction == LaserSlam.Direction.LEFT else 1
                            laser.node_type = LaserCont.END
                            laser_end = LaserNode(laser)
                            event = LaserSlam(laser_start, laser_end) # TODO what uhhh the fuck, TODO persist for later
                            self.events[now][(EventKind.TRACK, track)] = event
                        else:
                            laser = LaserNode(laser)
                            self.events[now][(EventKind.TRACK, track)] = laser
                for button in Button:
                    if ksh_line.buttons[button] == KshLine.ButtonState.HOLD:
                        event = ButtonPress(button, 69, 3) # TODO get duration, TODO effects
                        self.events[now][(EventKind.TRACK, button.to_track_num())] = event
                    elif ksh_line.buttons[button] == KshLine.ButtonState.PRESS:
                        self.events[now][(EventKind.TRACK, button.to_track_num())] = ButtonPress(button, 0, 3) # TODO effects
                now.add(1, timesig)

        # TODO effect defines

        self.finalized = True

    def write_to_vox(self, file=sys.stdout):
        def p(*args, **kwargs):
            print(*args, **kwargs, file=file)

        p('// made by ksh2vox')
        p('')

        p('#FORMAT VERSION')
        p('10')
        p('#END')
        p('')

        p('#BEAT INFO')
        for now, events in self.events.items():
            if EventKind.TIMESIG in events:
                event = events[EventKind.TIMESIG]
                p(f'{now.to_time_str()}\t{event.top}\t{event.bottom}')
        p('#END')
        p('')

        p('#BPM INFO')
        for now, events in self.events.items():
            if EventKind.BPM in events:
                # TODO what the fuck is a stop event
                bpm = events[EventKind.BPM]
                p(f'{now.to_time_str()}\t{bpm}\t4')
        p('#END')
        p('')

        p('#TILT MODE INFO')
        for now, events in self.events.items():
            if EventKind.TILTMODE in events:
                mode = events[EventKind.TILTMODE].to_vox_id()
                p(f'{now.to_time_str()}\t{mode}')
        p('#END')
        p('')

        p('#END POSITION')
        end = max(self.events.keys())
        p(f'{end.to_time_str()}')
        p('#END')
        p('')

        # TODO tab effects

        # TODO fx button effects

        # TODO tab param assigns

        def laser_track(i):
            p('#TRACK' + str(i))
            for now, events in self.events.items():
                if (EventKind.TRACK, i) in events:
                    event = events[(EventKind.TRACK, i)]
                    if isinstance(event, LaserSlam):
                        lasers = [event.start, event.end]
                    else:
                        lasers = [event]
                    for laser in lasers:
                        position = laser.position
                        node_type = laser.node_cont.value
                        if laser.roll_kind is None:
                            roll_kind = 0
                        else:
                            roll_kind = laser.roll_kind.value
                        # TODO filter and range
                        p(f'{now.to_time_str()}\t{position}\t{node_type}\t{roll_kind}')
            p('#END')
            p('')

        def button_track(i):
            p('#TRACK' + str(i))
            for now, events in self.events.items():
                if (EventKind.TRACK, i) in events:
                    event: ButtonPress = events[(EventKind.TRACK, i)]
                    duration = event.duration
                    if event.button.is_fx():
                        if duration > 0:
                            fx_data = event.effect + 2
                        else:
                            fx_data = event.effect
                        p(f'{now.to_time_str()}\t{duration}\t{fx_data}')
                    else:
                        p(f'{now.to_time_str()}\t{duration}')
            p('#END')
            p('')

        laser_track(1)
        button_track(2)
        button_track(3)
        button_track(4)
        button_track(5)
        button_track(6)
        button_track(7)
        laser_track(8)

        # TODO sp controller shit

    def close(self):
        self.kshfile.close()


METADATA_FIX = [
    ['\u203E', '~'],
    ['\u301C', '～'],
    ['\u49FA', 'ê'],
    ['\u5F5C', 'ū'],
    ['\u66E6', 'à'],
    ['\u66E9', 'è'],
    ['\u7F47', 'ê'],
    ['\u8E94', '🐾'],
    ['\u9A2B', 'á'],
    ['\u9A69', 'Ø'],
    ['\u9A6B', 'ā'],
    ['\u9A6A', 'ō'],
    ['\u9AAD', 'ü'],
    ['\u9B2F', 'ī'],
    ['\u9EF7', 'ē'],
    ['\u9F63', 'Ú'],
    ['\u9F67', 'Ä'],
    ['\u973B', '♠'],
    ['\u9F6A', '♣'],
    ['\u9448', '♦'],
    ['\u9F72', '♥'],
    ['\u9F76', '♡'],
    ['\u9F77', 'é'],
    ['?壬', 'êp']
]

CASES = {
    'basic': (781, 'm'),
    'laser-range': (1138, 'e'),
    'laser-range-refreshing-fix': (980, 'e'),
    'laser-effect-6': (122, 'i'),
    'choppy-laser': (1332, 'a'),
    'slam-range': (529, 'e'),
    'time-signature': (56, 'i'),
    'time-six-eight': (744, 'e'),
    'bpm': (262, 'n'),
    'early-version': (1, 'n'),
    'encoding': (656, 'e'),
    'diff-preview': (26, 'i'),
    'new-fx': (1, 'i'),
    'crash-fx': (1208, 'e'),
    'double-fx': (1136, 'a'),
    'highpass-fx': (1014, 'm'),
    'old-vox-retrigger-fx': (71, 'e'),
    'fx-chip-sound': (1048, 'm'),
    'basic-rolls': (271, 'e'),
    'camera': (250, 'i'),
    'tilt-mode': (34, 'i'),
    'spc-tilt': (71, 'i'),
    'wtf': (1361, 'm'),
    'removed-data': (233, 'e'),
    'timesig-stop': (1148, 'm'),
    'laser-centering': (1244, 'm')
}

thread_id_index = {}
def thread_print(line):
    if threading.get_ident() not in thread_id_index:
        thread_id_index[threading.get_ident()] = len(thread_id_index) + 1
    print(f'{thread_id_index[threading.get_ident()]}> {line}')

def do_process_kshfiles(files):
    global args

    # Load source directory.
    for ksh_path in files:
        try:
            debug().state = Debug.State.INPUT
            debug().input_filename = ksh_path
            debug().output_filename = None
            debug().reset()

            # noinspection PyBroadException
            try:
                ksh = Ksh.from_file(ksh_path)
            except Exception:
                debug().record_last_exception(level=Debug.Level.ERROR, tag='ksh_load')
                continue

            thread_print(f'Processing "{ksh_path}"')

            start_time = time.time()

            # First try to parse the file.
            try:
                ksh.parse()
            except Exception as e:
                thread_print(f'Parsing ksh file failed with "{str(e)}":\n{traceback.format_exc()}')
                debug().record_last_exception(level=Debug.Level.ERROR, tag='ksh_parse', trace=True)
                continue

            # Make the output directory.
            print(ksh.metadata)
            song_dir = f'out/{to_path(ksh.metadata["title"])}'
            if not os.path.isdir(song_dir):
                thread_print(f'Creating song directory "{song_dir}".')
                os.mkdir(song_dir)

            jacket_idx = None
            using_difficulty_audio = None

            # Copy media files over.
            #if args.do_media:
            #    using_difficulty_audio = do_copy_audio(ksh, song_dir)
            #    jacket_idx = do_copy_jacket(ksh, song_dir)
#
            #    # Copy FX chip sounds.
            #    if len(ksh.required_chip_sounds) > 0:
            #        do_copy_fx_chip_sounds(ksh, song_dir)

            # Output the VOX chart.
            chart_path = f'{song_dir}/{ksh.source_file_name}.vox'

            debug().output_filename = chart_path
            debug().state = Debug.State.OUTPUT

            if args.do_convert:
                thread_print(f'Writing VOX data to "{chart_path}".')
                with open(chart_path, "w+", encoding='utf-8') as ksh_file:
                    try:
                        ksh.write_to_vox(jacket_idx=jacket_idx,
                                         using_difficulty_audio=using_difficulty_audio,
                                         file=ksh_file)
                    except Exception as e:
                        print(f'Outputting to vox failed with "{str(e)}"\n{traceback.format_exc()}\n')
                        debug().record_last_exception(level=Debug.Level.ERROR, tag='vox_output', trace=True)
                        continue
                    duration = time.time() - start_time
                    if debug().has_issues():
                        exceptions = debug().exceptions_count
                        thread_print(f'Finished conversion in {truncate(duration, 4)}s with {exceptions[Debug.Level.ABNORMALITY]} abnormalities, {exceptions[Debug.Level.WARNING]} warnings, and {exceptions[Debug.Level.ERROR]} errors.')
                    else:
                        thread_print(f'Finished conversion in {truncate(duration, 4)}s with no issues.')
            else:
                thread_print(f'Skipping conversion step.')
            ksh.close()
        except Exception as e:
            debug().record_last_exception(Debug.Level.ERROR, 'other', f'an error occurred: {str(e)}')

def do_copy_audio(vox, out_dir):
    """
    Search for and copy the track's audio file to the output directory.
    :return: True if the audio file is difficulty-specific, otherwise False.
    """
    global args

    using_difficulty_audio = False

    target_audio_path = f'{out_dir}/track.ogg'

    src_audio_path = f'{args.audio_dir}/{vox.song_id}_{vox.difficulty.to_abbreviation()}{AUDIO_EXTENSION}'

    if not os.path.exists(src_audio_path):
        src_audio_path = f'{args.audio_dir}/{vox.song_id}{AUDIO_EXTENSION}'
    else:
        using_difficulty_audio = True
        target_audio_path = f'{out_dir}/track_{vox.difficulty.to_abbreviation()}{AUDIO_EXTENSION}'
        thread_print(f'Found difficulty-specific audio "{src_audio_path}".')

    if not os.path.exists(src_audio_path):
        raise KshLoadError('no audio file found')

    if not os.path.exists(target_audio_path):
        thread_print(f'Copying audio file "{src_audio_path}" to song directory.')
        shutil.copyfile(src_audio_path, target_audio_path)
    else:
        thread_print(f'Audio file "{target_audio_path}" already exists.')

    return using_difficulty_audio

def do_copy_jacket(vox, out_dir):
    """
    Find and copy the jacket image file for this vox to the output directory.
    :return: The index of the jacket used by this vox.
    """
    global args

    src_jacket_path = f'{args.jacket_dir}/{vox.song_id}_{vox.difficulty.to_jacket_ifs_numer()}.png'

    if os.path.exists(src_jacket_path):
        target_jacket_path = f'{out_dir}/jacket_{str(vox.difficulty.to_jacket_ifs_numer())}.png'
        thread_print(f'Jacket image file found at "{src_jacket_path}". Copying to "{target_jacket_path}".')
        shutil.copyfile(src_jacket_path, target_jacket_path)
    else:
        thread_print(f'Could not find jacket image file. Checking easier diffs.')
        fallback_jacket_diff_idx = vox.difficulty.to_jacket_ifs_numer() - 1

        while True:
            if fallback_jacket_diff_idx < 0:
                thread_print('No jackets found for easier difficulties either. Leaving jacket blank.')
                debug().record(Debug.Level.WARNING, 'copy_jacket', 'could not find any jackets to copy')
                return None

            easier_jacket_path = f'{args.jacket_dir}/{vox.song_id}_{fallback_jacket_diff_idx}.png'
            target_jacket_path = f'{out_dir}/jacket_{fallback_jacket_diff_idx}.png'
            if os.path.exists(easier_jacket_path):
                # We found the diff number with the jacket.
                thread_print(f'Using jacket "{easier_jacket_path}".')
                shutil.copyfile(easier_jacket_path, target_jacket_path)
                return fallback_jacket_diff_idx
            fallback_jacket_diff_idx -= 1

    return vox.difficulty.to_jacket_ifs_numer()

def do_copy_preview(vox, out_dir):
    """
    Find and copy the preview for this vox to the output directory.
    :return: True if this chart has a difficulty-specific preview file, False otherwise.
    """
    global args

    output_path = f'{out_dir}/preview{AUDIO_EXTENSION}'
    preview_path = f'{args.preview_dir}/{vox.song_id}{AUDIO_EXTENSION}'
    diff_preview_path = f'{splitx(preview_path)[0]}_{vox.difficulty.to_abbreviation()}{AUDIO_EXTENSION}'
    using_difficulty_preview = False

    if os.path.exists(diff_preview_path):
        preview_path = diff_preview_path
        output_path = f'{splitx(output_path)[0]}_{vox.difficulty.to_abbreviation()}{splitx(output_path)[1]}'
        using_difficulty_preview = True

    if os.path.exists(output_path):
        thread_print(f'Preview file "{output_path}" already exists.')
        return using_difficulty_preview

    if os.path.exists(preview_path):
        thread_print(f'Copying preview to "{output_path}".')
        shutil.copyfile(preview_path, output_path)
    else:
        print('> No preview file found.')
        debug().record(Debug.Level.WARNING, 'preview_copy', 'could not find preview file')
        return None

    return using_difficulty_preview

def do_copy_fx_chip_sounds(vox, out_dir):
    """ For each FX chip sound used in the chart, copy the sound file to the output directory. """
    global args

    thread_print(f'Copying FX chip sounds {vox.required_chip_sounds}.')
    for sound in vox.required_chip_sounds:
        src_path = f'{args.fx_chip_sound_dir}/{sound}{FX_CHIP_SOUND_EXTENSION}'
        target_path = f'{out_dir}/fxchip_{sound}{FX_CHIP_SOUND_EXTENSION}'
        if os.path.exists(src_path):
            shutil.copyfile(src_path, target_path)
        else:
            debug().record(Debug.Level.ERROR, 'copy_fx_chip_sound', f'cannot find file for chip sound with id {sound}')
            shutil.copyfile(f'{args.fx_chip_sound_dir}/0{FX_CHIP_SOUND_EXTENSION}', target_path)

def debug():
    global debugs

    if threading.get_ident() not in debugs:
        debugs[threading.get_ident()] = Debug(f'debug/exceptions_{threading.get_ident()}.txt')
    return debugs[threading.get_ident()]

##############
# PROGRAM RUNTIME BEGINS BELOW
#############

args = None
debugs = {}

def main():
    if not os.path.exists('config.ini'):
        print('Please create a config.ini based off the provided sample.', file=sys.stderr)
        sys.exit(1)
    global args
    argparser = argparse.ArgumentParser(description='Convert ksh to vox')
    argparser.add_argument('-j', '--num-cores', default=1, type=int)
    argparser.add_argument('-t', '--testcase')
    argparser.add_argument('-i', '--song-id')
    argparser.add_argument('-d', '--song-difficulty')
    argparser.add_argument('-n', '--no-media', action='store_false', dest='do_media')
    argparser.add_argument('-m', '--no-convert', action='store_false', dest='do_convert')
    argparser.add_argument('-x', '--no-merge-db', action='store_false', dest='multi_db')
    argparser.add_argument('-K', '--ksh-dir', default='D:/SDVX-Import/ksh')
    argparser.add_argument('-D', '--db-dir', default='D:/SDVX-Import/music_db')
    argparser.add_argument('-A', '--audio-dir', default='D:/SDVX-Import/song_prepared')
    argparser.add_argument('-C', '--fx-chip-sound-dir', default='D:/SDVX-Import/fx_chip_sound')
    argparser.add_argument('-J', '--jacket-dir', default='D:/SDVX-Import/jacket')
    argparser.add_argument('-P', '--preview-dir', default='D:/SDVX-Import/preview')
    argparser.add_argument('-c', '--clean-output', action='store_true', dest='do_clean_output')
    argparser.add_argument('-e', '--clean-debug', action='store_true', dest='do_clean_debug')
    args = argparser.parse_args()

    if args.testcase:
        if not args.testcase in CASES:
            print('please specify a valid testcase', file=sys.stderr)
            print('valid testcases are:', file=sys.stderr)
            for c in CASES.keys():
                print('\t' + c, file=sys.stderr)
            exit(1)

    # Create output directory.
    if args.do_clean_output:
        print('Cleaning directory of old charts.')
        shutil.rmtree('out')
    if not os.path.exists('out'):
        print(f'Creating output directory.')
        os.mkdir('out')

    if args.do_clean_debug:
        print('Cleaning directory of debug output.')
        shutil.rmtree('debug')
    if not os.path.exists('debug'):
        print(f'Creating debug output directory.')
        os.mkdir('debug')

    candidates = []

    print(f'Finding ksh files.')

    for filename in glob(f'{args.ksh_dir}/*.ksh'):
        import re
        if (args.song_id is None and args.testcase is None) or \
                (args.song_id is not None and f'_{args.song_id.zfill(4)}_' in filename) or \
                (args.testcase is not None and re.match(rf'^.*00[1-4]_0*{CASES[args.testcase][0]}_.*{CASES[args.testcase][1]}\.ksh$', filename)):
            if args.song_difficulty is None or splitx(filename)[0][-1] == args.song_difficulty:
                # See if this is overriding an earlier game's version of the chart.
                try:
                    prev: str = next(filter(lambda n: n.split('_')[1] == filename.split('_')[1] and splitx(n)[0][-1] == splitx(filename)[0][-1], candidates))
                    if int(prev.split('_')[1]) < int(filename.split('_')[1]):
                        candidates.remove(prev)
                    else:
                        continue
                except StopIteration:
                    # Not clashing with anything.
                    pass
                except (IndexError, ValueError):
                    # Malformed file name.
                    pass

                candidates.append(filename)

    print('The following files will be processed:')
    for f in candidates:
        print(f'\t{f}')

    groups = [[] for _ in range(args.num_cores)]
    for i, candidate in enumerate(candidates):
        try:
            song_id = os.path.basename(candidate).split('_')[1]
            groups[int(song_id) % args.num_cores].append(candidate)
        except (ValueError, IndexError):
            groups[i % args.num_cores].append(candidate)

    threads = []

    global debugs

    for i in range(args.num_cores):
        thread = threading.Thread(target=do_process_kshfiles, args=(groups[i],), name=f'Thread-{i}')
        threads.append(thread)

    print(f'Performing conversion across {args.num_cores} threads.')

    for t in threads:
        t.start()
    for t in threads:
        t.join()
    for d in debugs.values():
        d.close()

if __name__ == '__main__':
    main()
