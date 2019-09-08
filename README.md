# vox2ksh

This converts `.vox` charts to `.ksh` charts. If you don't know what those are then this repo is not for you.

## Prerequisites

The paths of the chart files and associated data must match the following requirements. For audio files, the 
`extractor.py` script in this repo will extract the data in the correct naming convention. Note that `extractor.py` 
will extract the songs to the `.wav` format; you must convert them to `.ogg`. An example:

```bash
# In the directory with the output WAVs for previews or tracks.
for f in *.wav; do ffmpeg -i "$f" -q:a 7 "${f%wav}ogg"; done
```

Obviously this requires `ffmpeg` to be installed.

#### Charts

These should be in the format given by running [ifstools](https://github.com/mon/ifstools) on the game's vox IFS files.
Upon extraction, the files will be in a number of `vox_<xx>_ifs` directories. Move all vox files within those 
directories into the one specified by the `--vox-dir` flag. There should be no subdirectories within that directory; a 
path to a chart would be `<vox-dir>/<a chart>.vox`.

#### Songs

Songs go in the directory specified by the `--audio-dir` flag. They must all be in one folder, with names in the format 
`<song id>.ogg`. Songs with extra **INF** audio should have said audio file named `<song id>_4i.ogg`. This ID should not
have any leading zeroes. So, the audio file for song with ID 25 would be `25.ogg`.

#### Previews

Previews follow the same convention as the songs but in the directory specified by `--preview-dir`.

#### FX Chip Sounds

Place these files in the directory specified by the `--fx-chip-sound-dir` flag. They should be named in the same order 
they came out of the IFS archive, which can be found in the same directory as the song audio. Their extension should be 
the same as the rest of the audio files.

#### Jackets

Jackets belong in the directory specified by the `--jacket-dir` flag. Their names should follow the format 
`<song id>_<difficulty index>`, where the `difficulty index` is its 1-indexed position in the difficulty order
(**NOV**, **ADV**, **EXH**, **INF**, **MXM**). So, the **ADV** jacket for the song with ID 501 would be `501_2.png`.

#### Metadata

Place the `music_db.xml` in the `data` directory. It can be found in the same directory as the source IFS files.

## Usage

Just running `converter.py` with Python 3 should begin converting the charts. The `--testcase` argument can be used to
convert a specific testcase (run it with no argument to list available testcases). The `--song-id` argument can be used
to convert the song with the specified ID. Run `converter.py -h` to see all options, including their short forms.

## Other

This software is provided for educational purposes only.