from enum import Enum, auto
from collections import namedtuple
from recordclass import dataobject
from xml.etree import ElementTree
from shutil import copyfile
import traceback
import random
import math

import sys, os
import argparse

TICKS_PER_BEAT = 48

pprint_prefix = ''

def pprint(*args, **kwargs):
    print('(' + pprint_prefix + ') '.join(map(str, args)), **kwargs)

TimeSignature = namedtuple('TimeSignature', 'top bottom')

class VoxNameError(Exception):
    pass
class MetadataFindError(Exception):
    pass
class AudioFileFindError(Exception):
    pass
class LaserNodeFormatError(Exception):
    pass
class ButtonEventError(Exception):
    pass
class KshConversionError(Exception):
    pass

class Timing:
    def __init__(self, measure, beat, offset):
        self.measure = measure
        self.beat = beat
        self.offset = offset

    @classmethod
    def from_time_str(cls, time: str):
        """ Create a Timing from the format string that appears in the first column of vox tracks. """
        splitted = time.split(',')
        if int(splitted[2]) >= TICKS_PER_BEAT:
            raise ValueError('offset greater than maximum')
        return cls(int(splitted[0]), int(splitted[1]), int(splitted[2]))

    # TODO I think most of these could be implemented better.
    def __eq__(self, other):
        return self.measure == other.measure and self.beat == other.beat and self.offset == other.offset

    def __hash__(self):
        return hash((self.measure, self.beat, self.offset))

    def __str__(self):
        return '{},{},{}'.format(self.measure, self.beat, self.offset)

    def __cmp__(self, other):
        if self.measure == other.measure:
            if self.beat == other.beat:
                return self.offset - other.offset
            return self.beat - other.beat
        return self.measure - other.measure

class CameraParam(Enum):
    @classmethod
    def from_vox_name(cls, vox_name):
        if vox_name == 'CAM_RotX':
            return cls.ROT_X
        elif vox_name == 'CAM_Radi':
            return cls.RAD_I
        else:
            return None

    def to_ksh_name(self):
        if self == self.ROT_X:
            return 'zoom_top'
        elif self == self.RAD_I:
            return 'zoom_bottom'

    def scaling_factor(self):
        if self == self.ROT_X:
            return 150.0
        elif self == self.RAD_I:
            return -150.0

    ROT_X = auto()
    RAD_I = auto()

class KshootEffect(Enum):
    def to_ksh_name(self, params):
        if self == KshootEffect.RETRIGGER:
            division = 8 if params is None else params['division']
            return f'Retrigger;{division}'

        elif self == KshootEffect.GATE:
            division = 8 if params is None else params['division']
            return f'Gate;{division}'

        elif self == KshootEffect.FLANGER:
            return 'Flanger'

        elif self == KshootEffect.BITCRUSHER:
            degree = 10 if params is None else params['degree']
            return f'BitCrusher;{degree}'

        elif self == KshootEffect.PHASER:
            return 'Phaser'

        elif self == KshootEffect.WOBBLE:
            division = 12 if params is None else params['division']
            return f'Wobble;{division}'

        elif self == KshootEffect.PITCHSHIFT:
            tones = 12 if params is None else params['tones']
            return f'PitchShift;{tones}'

        elif self == KshootEffect.TAPESTOP:
            speed = 50 if params is None else params['speed']
            return f'TapeStop;{speed}'

        elif self == KshootEffect.ECHO:
            # TODO Figure out echo parameters.
            x = 4 if params is None else params['x']
            y = 60 if params is None else params['y']
            return f'Echo;{x};{y}'

        elif self == KshootEffect.SIDECHAIN:
            return 'SideChain'

    @classmethod
    def from_pre_v4_vox_sound_id(cls, sound_id):
        if sound_id < 2:
            if sound_id == 1:
                print('A chart used 0bt_2mix. Please make sure the chart was "pulse_laser_higedriver_1n".')
            return None
        elif sound_id == 2:
            return cls.RETRIGGER, {"division": 8}
        elif sound_id == 3:
            return cls.RETRIGGER, {"division": 16}
        elif sound_id == 4:
            return cls.GATE, {"division": 16}
        elif sound_id == 5:
            return cls.FLANGER
        elif sound_id == 6:
            return cls.RETRIGGER, {"division": 32}
        elif sound_id == 7:
            return cls.GATE, {"division": 8}
        elif sound_id == 8:
            return cls.PITCHSHIFT
        else:
            raise ValueError(f'Pre-v4 vox sound id {sound_id} does not exist.')

    RETRIGGER = auto()
    GATE = auto()
    FLANGER = auto()
    BITCRUSHER = auto()
    PHASER = auto()
    WOBBLE = auto()
    PITCHSHIFT = auto()
    TAPESTOP = auto()
    ECHO = auto()
    SIDECHAIN = auto()

class Button(Enum):
    BT_A = auto()
    BT_B = auto()
    BT_C = auto()
    BT_D = auto()
    FX_L = auto()
    FX_R = auto()

    def is_fx(self):
        return self == Button.FX_L or self == Button.FX_R

    @classmethod
    def from_track_num(cls, num: int):
        if num == 2:
            return cls.FX_L
        elif num == 3:
            return cls.BT_A
        elif num == 4:
            return cls.BT_B
        elif num == 5:
            return cls.BT_C
        elif num == 6:
            return cls.BT_D
        elif num == 7:
            return cls.FX_R
        else:
            raise ValueError('invalid track number for button: {}'.format(num))

class ButtonPress:
    def __init__(self, time: Timing, button: Button, duration: int, effect: (KshootEffect, dict)):
        self.time = time
        self.button = button
        self.duration = duration
        self.effect = effect

LaserRangeChange = namedtuple('LaserRangeChange', 'time side range')

class LaserSide(Enum):
    LEFT = auto()
    RIGHT = auto()

    def as_letter(self):
        return 'l' if self == LaserSide.LEFT else 'r'

class LaserCont(Enum):
    """ The continuity status of a laser node. """
    CONTINUE = 0
    START = 1
    END = 2

class LaserNode:
    class Builder(dataobject):
        time: Timing = None
        side: LaserSide = None
        position: int = None
        node_type: LaserCont = None
        range: int = 1

    def __init__(self, builder: Builder):
        self.time = builder.time
        self.side = builder.side
        self.position = builder.position
        self.node_type = builder.node_type
        self.range = builder.range

    def position_ksh(self):
        """ Convert the position from the 7-bit scale to whatever the hell KSM is using. """
        chars = []
        for char in range(10):
            chars.append(chr(ord('0') + char))
        for char in range(24):
            chars.append(chr(ord('A') + char))
        for char in range(15):
            chars.append(chr(ord('a') + char))
        idx = math.floor((self.position / 127) * (len(chars) - 1))
        return chars[idx]

class LaserSlam:
    def __init__(self, start: LaserNode, end: LaserNode):
        if start.time != end.time:
            raise ValueError('start time {} differs from end time {}'.format(start.time, end.time))
        self.start = start
        self.end = end
        self.time = start.time

class Difficulty(Enum):
    NOVICE = 0
    ADVANCED = 1
    EXHAUST = 2
    MAXIMUM = 3
    INFINITE = 4
    # TODO GRV and HVN?

    @classmethod
    def from_letter(cls, letter):
        """ Derive value from the last letter of the vox filename. """
        if letter == 'n':
            return cls.NOVICE
        elif letter == 'a':
            return cls.ADVANCED
        elif letter == 'e':
            return cls.EXHAUST
        elif letter == 'm':
            return cls.MAXIMUM
        elif letter == 'i':
            return cls.INFINITE
        else:
            raise ValueError('invalid letter for difficulty: {}'.format(letter))

    def to_ksh_name(self):
        """ Convert to a name recognized by KSM. """
        if self == self.NOVICE:
            return 'novice'
        elif self == self.ADVANCED:
            return 'challenge'
        elif self == self.EXHAUST:
            return 'extended'
        elif self == self.MAXIMUM or self == self.INFINITE:
            return 'infinite'

    def to_xml_name(self):
        if self == self.NOVICE:
            return 'novice'
        elif self == self.ADVANCED:
            return 'advanced'
        elif self == self.EXHAUST:
            return 'exhaust'
        elif self == self.MAXIMUM:
            return 'maximum'
        elif self == self.INFINITE:
            return 'infinite'

    def to_jacket_ifs_numer(self):
        if self == self.NOVICE:
            return 1
        elif self == self.ADVANCED:
            return 2
        elif self == self.EXHAUST:
            return 3
        elif self == self.MAXIMUM:
            return 4
        else:
            return 5

class ParserError(Exception):
    """ Exception raised when the Vox parser encounters invalid syntax. """
    def __init__(self, message, filename, line):
        super().__init__(f'({filename}:{str(line)} {message}')

class Vox:
    class State(Enum):
        @classmethod
        def from_token(cls, token):
            if token.startswith('=') or token.startswith(' '):
                return None
            elif token == 'END':
                return cls.NONE
            if token == 'FORMAT VERSION':
                return cls.FORMAT_VERSION
            elif token == 'BPM':
                return cls.BPM
            elif token == 'BPM INFO':
                return cls.BPM_INFO
            elif token == 'BEAT INFO':
                return cls.BEAT_INFO
            elif token == 'END POSISION' or token == 'END POSITION':
                return cls.END_POSITION
            elif token == 'SOUND ID START':
                return cls.SOUND_ID
            elif token == 'SPCONTROLLER':
                return cls.SPCONTROLLER
            elif token == 'TRACK AUTO TAB':
                return None
            elif token.startswith('TRACK'):
                return cls.TRACK, int(token[5])

        NONE = auto()
        FORMAT_VERSION = auto()
        BPM = auto()
        BPM_INFO = auto()
        BEAT_INFO = auto()
        END_POSITION = auto()
        SOUND_ID = auto()
        TRACK = auto()
        SPCONTROLLER = auto()

    def __init__(self):
        self.voxfile = None
        self.game_id = 0
        self.song_id = 0
        self.vox_version = 0
        self.defines = {}
        self.time_sigs = {}
        self.bpms = {}
        self.camera_changes = {}
        self.end = None
        self.events = []

        self.state = None
        self.state_track = 0

        self.metadata: ElementTree = None
        self.difficulty = None

    def get_metadata(self, tag, from_diff=False):
        if from_diff:
            the_diff = None
            for diff in self.metadata.find('difficulty').iter():
                if diff.tag == self.difficulty.to_xml_name():
                    the_diff = diff
                    break
            if the_diff is None:
                raise LookupError('difficulty {} not found in the `music` element'.format(self.difficulty.to_xml_name()))
            return the_diff.find(tag).text
        return self.metadata.find('info').find(tag).text

    def bpm_string(self):
        # TODO Make sure decimal BPM's are okay.
        if self.get_metadata('bpm_min') == self.get_metadata('bpm_max'):
            return int(int(self.get_metadata('bpm_min')) / 100)
        else:
            return f"{int(int(self.get_metadata('bpm_min')) / 100)}-{int(int(self.get_metadata('bpm_max')) / 100)}"

    def process_state(self, line, filename=None, line_no=None):
        splitted = line.split('\t')

        if self.state == self.State.FORMAT_VERSION:
            self.vox_version = int(line)
        elif self.state == self.State.BEAT_INFO:
            timesig = TimeSignature(int(splitted[1]), int(splitted[2]))
            self.time_sigs[Timing.from_time_str(splitted[0])] = timesig
        elif self.state == self.State.BPM:
            self.bpms[Timing(1, 1, 0)] = float(line)
        elif self.state == self.State.BPM_INFO:
            self.bpms[Timing.from_time_str(splitted[0])] = splitted[1]
            # TODO There's at least a third column.
        elif self.state == self.State.END_POSITION:
            self.end = Timing.from_time_str(line)
        elif self.state == self.State.SOUND_ID:
            raise ParserError('non-define line encountered in SOUND ID', filename, line_no)
        elif self.state == self.State.SPCONTROLLER:
            param = CameraParam.from_vox_name(splitted[1])
            self.camera_changes[(Timing.from_time_str(splitted[0]), param)] = float(splitted[4])
        elif self.state == self.state.TRACK:
            if self.state_track == 1 or self.state_track == 8:
                laser_node = LaserNode.Builder()
                laser_node.time = Timing.from_time_str(splitted[0])
                laser_node.side = LaserSide.LEFT if self.state_track == 1 else LaserSide.RIGHT
                laser_node.position = int(splitted[1])
                laser_node.node_type = LaserCont(int(splitted[2]))
                if len(splitted) > 5:
                    laser_node.range = int(splitted[5])
                laser_node = LaserNode(laser_node)

                if laser_node.position > 127 or laser_node.position < 0:
                    raise LaserNodeFormatError(f'position {laser_node.position} is out of bounds')

                # Check if it's a slam.
                slam_start = None
                for e in self.events:
                    if type(e) is LaserNode and e.side == laser_node.side and e.time == laser_node.time:
                        # We're gonna remove the laser node and replace it with a slam node.
                        slam_start = e
                        break
                if slam_start is None:
                    self.events.append(laser_node)
                else:
                    slam = LaserSlam(slam_start, laser_node)
                    self.events.remove(slam_start)
                    self.events.append(slam)
            else:
                try:
                    button = Button.from_track_num(self.state_track)
                    fx_data = None
                    if button.is_fx():
                        # Process effect assignment.
                        if self.vox_version < 4:
                            sound_id = int(splitted[3]) if splitted[3].isdigit() else int(self.defines[splitted[3]])
                            fx_res = KshootEffect.from_pre_v4_vox_sound_id(sound_id)
                            if type(fx_res) is tuple:
                                fx_data = (fx_res[0], fx_res[1])
                            else:
                                fx_data = (fx_res, None)

                    self.events.append(ButtonPress(Timing.from_time_str(splitted[0]), button, int(splitted[1]), fx_data))
                except ValueError:
                    raise ButtonEventError(f'{self.state_track} is an invalid button track')


    def as_ksh(self, file=sys.stdout, metadata_only=False, jacket_idx=None, progress_bar=True):
        # First print metadata.
        # TODO song file, preview, chokkaku, yomigana titles(?), background
        if jacket_idx is None:
            jacket_idx = str(self.difficulty.to_jacket_ifs_numer())
        print(f'''title={self.get_metadata('title_name')}
artist={self.get_metadata('artist_name')}
effect={self.get_metadata('effected_by', True)}
jacket={jacket_idx}.png
illustrator={self.get_metadata('illustrator', True)}
difficulty={self.difficulty.to_ksh_name()}
level={self.get_metadata('difnum', True)}
t={self.bpm_string()}
m=track.mp3
mvol={self.get_metadata('volume')}
o=0
bg=desert
layer=arrow
po=0
plength=15000
pfiltergain=50
filtertype=peak
chokkakuautovol=0
chokkakuvol=50
ver=167''', file=file)

        if metadata_only:
            return

        print('--', file=file)

        # Holds come in the pair <button>,<duration>
        holds = []
        lasers = {LaserSide.LEFT: False, LaserSide.RIGHT: False}
        slams = []
        current_timesig = self.time_sigs[Timing(1, 1, 0)]

        measure_iter = range(self.end.measure)
        if progress_bar:
            from tqdm import tqdm
            measure_iter = tqdm(measure_iter, unit='measure', leave=False)

        for m in measure_iter:
            measure = m + 1

            # Laser range resets every measure in ksh.
            laser_range = {LaserSide.LEFT: 1, LaserSide.RIGHT: 1}

            now = Timing(measure, 1, 0)

            if now in self.time_sigs:
                current_timesig = self.time_sigs[now]
                print(f'beat={current_timesig.top}/{current_timesig.bottom}', file=file)

            for b in range(current_timesig.top):
                # Vox beats are also 1-indexed.
                beat = b + 1

                for o in range(TICKS_PER_BEAT):
                    # However, vox offsets are 0-indexed.

                    now = Timing(measure, beat, o)

                    buffer = ''

                    if now.beat > 1 and now.offset > 0 and now in self.time_sigs:
                        raise KshConversionError('time signature change in the middle of a measure')

                    if now in self.bpms:
                        buffer += f't={str(self.bpms[now]).rstrip("0").rstrip(".").strip()}\n'

                    # Camera events.
                    for cam_param in CameraParam:
                        if (now, cam_param) in self.camera_changes:
                            the_change = self.camera_changes[(now, cam_param)]
                            buffer += f'{cam_param.to_ksh_name()}={int(the_change * cam_param.scaling_factor())}'

                    buttons_here = []
                    lasers_here = {LaserSide.LEFT: None, LaserSide.RIGHT: None}
                    for e in filter(lambda x: x.time == Timing(measure, beat, o), self.events):
                        # Check if it's a hold first.
                        if type(e) is ButtonPress and e.duration != 0:
                            if Button.is_fx(e.button):
                                letter = 'l' if e.button == Button.FX_L else 'r'
                                effect_string = e.effect[0].to_ksh_name(e.effect[1]) if e.effect is not None else \
                                    random.choice(list(KshootEffect)).to_ksh_name(None)
                                buffer += f'fx-{letter}={effect_string}\n'
                            holds.append([e.button, e.duration])
                        elif type(e) is ButtonPress:
                            buttons_here.append(e.button)
                        elif type(e) is LaserNode:
                            if e.range != laser_range[e.side]:
                                buffer += 'laserrange_{}={}x\n'.format(e.side.as_letter(), e.range)
                                laser_range[e.side] = e.range

                            lasers_here[e.side] = e
                            if e.node_type == LaserCont.START:
                                lasers[e.side] = True
                            elif e.node_type == LaserCont.END:
                                lasers[e.side] = False
                        elif type(e) is LaserSlam:
                            lasers_here[e.start.side] = e.start
                            # Slam tuple: <slam>,<ticks since slam start>
                            slams.append([e, 0])

                    # Print button state.
                    for btn in [
                        Button.BT_A,
                        Button.BT_B,
                        Button.BT_C,
                        Button.BT_D,
                        Button.FX_L,
                        Button.FX_R
                    ]:
                        yes = '2' if btn.is_fx() else '1'
                        no = '0'
                        hold = '1' if btn.is_fx() else '2'

                        # A bar separates BT from FX.
                        if btn == Button.FX_L:
                            buffer += '|'

                        if btn in buttons_here:
                            buffer += yes
                        elif btn in map(lambda h: h[0], holds):
                            buffer += hold
                        else:
                            buffer += no

                    buffer += '|'

                    # Now print laser state.
                    for lsr in [
                        LaserSide.LEFT,
                        LaserSide.RIGHT
                    ]:
                        slam = None
                        laser_cancel = False
                        for s in slams:
                            if s[0].start.side == lsr and (s[0].time == Timing(measure, beat, o) or s[1]):
                                slam = s
                                break
                        if slam is not None:
                            if slam[1] == 3:
                                buffer += slam[0].end.position_ksh()
                                slams.remove(slam)
                                if slam[0].end.node_type == LaserCont.END:
                                    lasers[lsr] = False
                                    laser_cancel = True
                            else:
                                lasers[lsr] = True
                                slam[1] += 1

                        if lasers_here[lsr] is not None:
                            buffer += lasers_here[lsr].position_ksh()
                        else:
                            if lasers[lsr] and not laser_cancel:
                                buffer += ':'
                            else:
                                # No laser event or ongoing laser.
                                buffer += '-'

                    print(buffer, file=file)

                    # Subtract time remaining from holds.
                    for hold in holds:
                        hold[1] -= 1
                    holds = list(filter(lambda h: h[1] > 0, holds))

            print('--', file=file)

    @classmethod
    def from_file(cls, path):
        parser = Vox()

        file = open(path, 'r')
        parser.voxfile = file

        filename_array = os.path.basename(path).split('_')
        with open('data/music_db.xml', encoding='shift_jisx0213') as db:
            try:
                parser.game_id = int(filename_array[0])
                parser.song_id = int(filename_array[1])
                parser.difficulty = Difficulty.from_letter(os.path.splitext(path)[0][-1])
            except ValueError:
                raise VoxNameError(f'unable to parse file name "{path}"')

            tree = ElementTree.fromstring(db.read()).findall('''.//*[@id='{}']'''.format(parser.song_id))

            if len(tree) == 0:
                raise MetadataFindError(f'unable to find metadata for song {parser.song_id}')

            parser.metadata = tree[0]

        if len(ID_TO_AUDIO) > 0:
            if not parser.song_id in ID_TO_AUDIO:
                raise AudioFileFindError(f'unable to find audio file for song {parser.song_id}')
        # else we chose to skip audio.

        return parser

    def parse(self):
        line_no = 1
        for line in self.voxfile:
            line = line.strip()
            if line.startswith('//'):
                continue
            if line.startswith('#'):
                token_state = self.State.from_token(line.split('#')[1])
                if token_state is None:
                    continue
                if type(token_state) is tuple:
                    self.state = token_state[0]
                    self.state_track = int(token_state[1])
                else:
                    self.state = token_state
            elif line.startswith('define'):
                splitted = line.split('\t')

                # Sanity check.
                if splitted[0] != 'define':
                    raise ParserError('illegal define line in SOUND ID', self.voxfile, line_no)
                if len(splitted) != 3:
                    raise ParserError('illegal number of operands in define statement', self.voxfile, line_no)

                self.defines[splitted[1]] = splitted[2]
            elif self.state is not None:
                self.process_state(line)
            line_no += 1

CASES = {
    'basic': 'data/vox_08_ifs/004_0781_alice_maestera_alstroemeria_records_5m.vox',
    'laser-range': 'data/vox_12_ifs/004_1138_newleaf_blackyooh_3e.vox',
    'time-signature': 'data/vox_01_ifs/001_0056_amanojaku_164_4i.vox',
    'early-version': 'data/vox_01_ifs/001_0001_albida_muryoku_1n.vox',
    'bpm': 'data/vox_03_ifs/002_0262_hanakagerou_minamotoya_1n.vox'
}

argparser = argparse.ArgumentParser(description='Convert vox to ksh')
argparser.add_argument('-t', '--testcase')
argparser.add_argument('-m', '--metadata-only', action='store_true')
argparser.add_argument('-a', '--audio-folder', default='D:\\SDVX-Extract (V0)')
argparser.add_argument('-j', '--jacket-folder', default='D:\\SDVX-Extract (jk)')
argparser.add_argument('-n', '--no-media', action='store_true')
argparser.add_argument('-c', '--convert', action='store_true')
args = argparser.parse_args()

ID_TO_AUDIO = {}

if not args.no_media:
    print('Generating audio file mapping...')
    # Audio files should have a name starting with the ID followed by a space.
    for _, _, files in os.walk(args.audio_folder):
        for f in files:
            if os.path.basename(f) == 'jk':
                continue
            try:
                ID_TO_AUDIO[int(os.path.basename(f).split(' ')[0])] = f
            except ValueError as e:
                print(e)
    print(f'{len(ID_TO_AUDIO)} songs processed.')

if args.testcase:
    if not args.testcase in CASES:
        print('please specify a valid testcase', file=sys.stderr)
        print('valid testcases are:', file=sys.stderr)
        for c in CASES.keys():
            print('\t' + c, file=sys.stderr)
        exit(1)
    vox = Vox.from_file(CASES[args.testcase])
    vox.parse()

    vox.as_ksh(file=open(f'{args.testcase}.ksh', "w+", encoding='utf-8') if not args.metadata_only else sys.stdout, metadata_only=args.metadata_only)

    exit(0)
elif args.convert:
    # Create output directory.
    if not os.path.exists('out'):
        print(f'Creating output directory.')
        os.mkdir('out')

    VOX_ROOT = 'data'

    # Load source directory.
    for d in filter(lambda x: os.path.isdir(VOX_ROOT + '/' + x), os.listdir(VOX_ROOT)):
        vox_dir = VOX_ROOT + '/' + d
        for f in os.listdir(vox_dir):
            vox_path = f'{vox_dir}/{f}'
            print(vox_path + ':')
            try:
                vox = Vox.from_file(vox_path)
            except (VoxNameError, MetadataFindError, AudioFileFindError) as e:
                print(f'> Skipping file "{vox_path}": {e}')
                continue

            print(f'> Processing {vox.song_id} "{vox.get_metadata("ascii")}" {vox.difficulty}.')

            # First try to parse the file.
            try:
                vox.parse()
            except Exception as e:
                print('> Parsing vox file failed with ' + str(e))
                continue

            game_dir = f'out/{str(vox.game_id).zfill(3)}'
            if not os.path.isdir(game_dir):
                print(f'> Making game directory "{game_dir}".')
                os.mkdir(game_dir)
            song_dir = f'{game_dir}/{vox.get_metadata("ascii")}'
            if not os.path.isdir(song_dir):
                print(f'> Creating song directory "{song_dir}".')
                os.mkdir(song_dir)

            fallback_jacket_diff_idx = None
            if not args.no_media:
                target_audio_path = song_dir + '/track.mp3'
                if not os.path.exists(target_audio_path):
                    src_audio_path = args.audio_folder + '/' + ID_TO_AUDIO[vox.song_id]
                    print(f'> Copying audio file {src_audio_path} to song directory.')
                    copyfile(src_audio_path, target_audio_path)
                else:
                    print(f'> Audio file "{target_audio_path}" already exists.')

                src_jacket_basename = f'jk_{str(vox.game_id).zfill(3)}_{str(vox.song_id).zfill(4)}_{vox.difficulty.to_jacket_ifs_numer()}_b'
                src_jacket_path = args.jacket_folder + '/' + src_jacket_basename + '_ifs/tex/' + src_jacket_basename + '.png'

                if os.path.exists(src_jacket_path):
                    target_jacket_path = f'{song_dir}/{str(vox.difficulty.to_jacket_ifs_numer())}.png'
                    print(f'> Jacket image file found at "{src_jacket_path}". Copying to "{target_jacket_path}".')
                    copyfile(src_jacket_path, target_jacket_path)
                else:
                    print(f'> Could not find jacket image file. Checking easier diffs.')
                    fallback_jacket_diff_idx = vox.difficulty.to_jacket_ifs_numer() - 1
                    while True:
                        if fallback_jacket_diff_idx < 0:
                            print('> No jackets found for easier difficulties either. Leaving jacket blank.')
                            fallback_jacket_diff_idx = ''
                            break

                        easier_jacket_path = f'{song_dir}/{fallback_jacket_diff_idx}.png'
                        if os.path.exists(easier_jacket_path):
                            # We found the diff number with the jacket.
                            print(f'> Using jacket "{easier_jacket_path}".')
                            break
                        fallback_jacket_diff_idx -= 1

            chart_path = f'{song_dir}/{vox.difficulty.to_xml_name()}.ksh'
            print(f'> Writing KSH data to "{chart_path}".')
            with open(chart_path, "w+", encoding='utf-8') as ksh_file:
                try:
                    vox.as_ksh(file=ksh_file, jacket_idx=str(fallback_jacket_diff_idx) if fallback_jacket_diff_idx is not None else None)
                except Exception as e:
                    print(f'Outputting to KSH failed with {e}. Traceback:\n{traceback.format_exc()}')
                    continue
                print('> Success!')
    exit(0)

print('Please specify something to do.')
exit(1)