# Animations of the proof landscape

The proof explorer is a web page, `index.html`, that draws the modules of the proof as a
landscape of dots. A tour file describes a camera run over that landscape, and `record_tour.py`
renders the run into an MP4 clip for a video. The same tour file also plays in the explorer page,
so a run can be watched and adjusted before it is rendered.

## Words used here

| Word | Meaning |
|---|---|
| module | One Lean file of the proof. The landscape draws it as a dot. |
| folder | A source folder that holds modules and other folders. The landscape draws it as a ring on the ground around its modules. |
| import | Module A imports module B when the file of A names the file of B in its import lines. |
| chain of imports | A list of modules in which each one imports the next. |
| rests on | Module A rests on module B when a chain of imports leads from A to B. |
| height | The height of a module is the number of modules in the longest chain of imports below it. One level is one step of height. |
| summit | The module at the top of the landscape, Main Conclusion, at height 198. |
| the page | The explorer page `index.html`. |
| the recorder | The script `record_tour.py`. |

## How the parts fit

| Part | What it does |
|---|---|
| `tours/*.json` | One tour file per clip. A tour is a list of steps, such as a view, a turn or a run along a chain of imports. |
| `tour.js` | Turns the steps into a timeline. Its function `Tour.seek(t)` sets the whole picture for the moment `t`, in seconds from the start of the tour. |
| `mountain.js` | Draws the picture on two canvases. One holds the modules as dots and the folders as rings. The other, called the overlay, lies over it and holds the folder names, the name of the summit, the trail of a chain and the caption. |
| `record_tour.py` | Opens the page in Chrome, asks it for every frame of the tour and hands the frames to ffmpeg. |

Playing a tour calls `Tour.seek` with the time that has passed since the tour began. Recording
calls it once per frame, with the moment that the frame stands for. A recorded clip therefore
shows the same camera run as the page, and it keeps an even speed however long a frame takes to
draw.

A clip holds what the two canvases hold. The buttons, the height legend and the panels of the
page are HTML, so they stay out of the clip.

## Seeing a tour in the page

Build the data as the [README](README.md) describes. Then serve the folder
`verification/explorer` with this command, run from the root of the repository.

```bash
cd verification/explorer && python3 -I -m http.server 8811 --bind 127.0.0.1
```

The server keeps running in that terminal. The page has three ways to show a tour:

- `http://127.0.0.1:8811/index.html` with the Follow chain button plays `tours/longest-chain.json`.
- `http://127.0.0.1:8811/index.html?tour=tours/ride-first-modules.json` makes the same button
  play the named tour.
- `http://127.0.0.1:8811/index.html?stage=1920x1080&tour=tours/longest-chain.json` shows the
  picture alone, in the proportions of a video frame of 1920 by 1080 pixels, and plays the tour
  once without a button press. This is the picture that the recorder renders.

In the first two ways, a bar under the buttons pauses the run, ends it and moves to any moment of
it, and shows the length of the tour. The path after `tour=` starts from the served folder.
Reload the page after editing a tour file.

In the first two ways the camera also moves by hand. A drag turns the mountain, a drag with
Shift held moves it sideways, and the scroll wheel zooms. The Mountain and Map buttons switch
between the raised mountain and the flat map, on which a drag moves the map.

## Recording a clip

Run the recorder from the root of the repository, in another terminal or after stopping the
server. The recorder serves the folder itself, on a port of its own. The path of the tour starts
from `verification/explorer`.

```bash
python3 -I verification/explorer/record_tour.py tours/longest-chain.json
```

The command writes `verification/explorer/clips/longest-chain.mp4`, at 1920 by 1080 pixels and
30 frames a second. It needs Google Chrome and ffmpeg. Chrome runs without a window and with its
own empty profile, which the recorder removes at the end.

| Option | Meaning | Default |
|---|---|---|
| `--size 3840x2160` | Frame size in pixels. | `1920x1080` |
| `--scale 4` | Pixels per unit of layout, as explained under the table. | `2` |
| `--fps 60` | Frames per second. | `30` |
| `--from 10 --to 16` | Render only this part of the tour, from second 10 to second 16. | the whole tour |
| `--out /path/clip.mp4` | The file to write. | the folder `clips/` in `verification/explorer`, with the tour's file name and the ending `.mp4` |
| `--crf 14` | Quality of the H.264 encoding, from 0 to 51. A lower number gives a better and larger file. | `18` |
| `--window` | Show the Chrome window while it draws. | no window |

The picture is laid out on a stage whose sides are the frame size divided by the scale. A frame
of 1920 by 1080 pixels at scale 2 has a stage of 960 by 540 units of layout, and the sizes of
text and dots are counted in these units. Text and dots keep their share of the frame when size
and scale grow together, so 3840 by 2160 pixels goes with scale 4.

The folder `clips/` is ignored by git. A cloud of dots compresses poorly, so the files are
large, and `--out` can put them on a disk with room.

On a MacBook Pro with an Apple M4 Pro processor, the two tours in `tours/` rendered like this at
the default settings:

| Tour | Length | Frames | Rendering time | File |
|---|---:|---:|---:|---:|
| `longest-chain.json` | 79.4 s | 2,383 | 52 s | 215 MB |
| `ride-first-modules.json` | 43.0 s | 1,291 | 35 s | 136 MB |

The recorder renders the first and the last moment of a tour, so a clip has one frame more than
its length times the frames per second.

The recorder stops with a sentence that names the cause when a tour file has an error, when
Chrome has no WebGL or when the page stops sending frames. Run the command again with `--window`
to see the page and its message.

The text in a clip uses the font Literata, which the page loads from Google Fonts. Without a
network connection the text falls back to Georgia, and the clip then differs from the page in
its type.

## The tour file

This is `tours/longest-chain.json` with shorter captions.

```json
{
  "title": "Down the longest chain of imports",
  "steps": [
    {"view": "mountain", "move": 0, "hold": 2, "caption": "175,174 modules under one theorem"},
    {"orbit": 30, "move": 6},
    {"chain": "longest", "move": 3, "hop": 0.3, "distance": 1.3, "hold": 2, "caption": "module"},
    {"view": "mountain", "move": 4, "hold": 3}
  ]
}
```

| Field of the tour | Meaning | Default |
|---|---|---|
| `title` | A name for people. `tour.js` ignores it. | none |
| `steps` | The steps, played in order. | required |
| `captions` | `false` leaves every caption out, for a clip that gets its text in the edit. | `true` |
| `labels` | `false` leaves out the folder names and the name of the summit. | `true` |

### Kinds of steps

A step carries one of the keys `view`, `pose`, `module`, `area`, `orbit` or `chain`, and that key
gives its kind. A step with none of them is a hold step.

| Step | The camera | What lights up |
|---|---|---|
| `{"view": "mountain"}` | Shows the whole landscape from the side, with each module raised by its height. | nothing new |
| `{"view": "map"}` | Shows the whole landscape from straight above, with the modules flat on the ground. | nothing new |
| `{"pose": {…}}` | Goes to a position given as camera numbers, which the section The camera numbers lists. | nothing new |
| `{"module": "Name"}` | Flies to the module and stops at a distance of 0.45 from it, or keeps its distance when it is already nearer. | The module in white, every module it rests on in orange and every module that rests on it in green. |
| `{"area": "Folder.Name"}` | Flies to the folder so that its ring fills the frame. | The folder's modules alone. |
| `{"orbit": 40}` | Turns 40 degrees around the point it looks at, at an even speed. Seen from above, the camera moves anticlockwise. A negative number moves it clockwise. | nothing new |
| `{"chain": …}` | Follows a chain of imports, as the section Chains describes. | The chain. |
| `{"hold": 2}` | Stays where it is for 2 seconds. | nothing new |

A module step names its module by the full Lean name, such as
`Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion`, or by the last part alone
when only one module ends with it. An area step names its folder the same way, such as
`Development.AbelianVarietyTheory`. The tour fails with a message when a name fits no module or
folder, or more than one.

What a step lights stays lit through the following steps, until another step lights something
else or a step carries `"select": false`. Such a step lights nothing itself and turns the earlier
light off when its move starts, so `{"module": "Name", "select": false}` flies to a module and
leaves it unlit. The last step of the example has no such field, so the chain stays lit in the
closing view.

### Time

Every step can carry a `move` and a `hold`. `move` is the number of seconds the camera travels to
the step's place, and on an orbit step it is the number of seconds of the turn. `hold` is the
number of seconds the camera then stays. A step that leaves `move` out gets 2 seconds, and a step
that leaves `hold` out gets none.

A move takes no time when the camera already stands at the step's place. A hold step therefore
lasts for its `hold` alone.

A chain step runs along its chain between its move and its hold. The steps follow each other
without gaps, so the length of a tour is the sum of the moves that take time, the holds and the
chain runs. The longest chain has 199 modules, so the chain run of the example makes 198 hops of
0.3 seconds, which is 59.4 seconds. The example lasts 2, then 6, then 3 and 59.4 and 2, then 4
and 3 seconds, which is 79.4 seconds. The bar of the page shows the length of a loaded tour, and
the recorder prints it at the end.

Start every tour with a view step, or with a pose step that gives all its numbers, and give that
step `"move": 0`. The first move otherwise starts from wherever the camera happens to be, and the
clip would differ from the run in the page.

### Fields that every step can carry

| Field | Meaning | Default |
|---|---|---|
| `move` | Seconds of travel to the step's place. | `2` |
| `hold` | Seconds to stay there. | `0` |
| `caption` | The text at the top left. A string gives one line. `{"title": "…", "text": "…"}` gives a title and a smaller line under it. `"module"` gives the name of the module that is lit, with its folder path. On a chain it names the module where the head is and adds that module's place in the chain. | no caption |
| `dim` | How far the unlit modules fade into the background while something is lit, from 0 for full colour to 1 for invisible. | `0.8` |
| `select` | `false` turns off what earlier steps lit. | keep it lit |
| `camera` | Camera numbers that replace single numbers of the place that the step sets. `{"d": 0.2}` on a module step brings the camera to a distance of 0.2 from the module. | none |
| `maxDot` | The size of the largest dot, in units of layout. A smaller number keeps near modules from covering the frame. | `256`, and `24` on a ride |

`caption`, `dim`, `camera` and `maxDot` apply to their own step alone, through its move, its
chain run and its hold. A ride is a chain step with the field `ride`, which the section Chains
describes.

### The camera numbers

The camera looks at a point and stands at a distance from it. The Copy camera button of the page
writes the current position as a ready pose step, shows it under the buttons and puts it on the
clipboard.

| Number | Meaning |
|---|---|
| `tx`, `ty` | The point the camera looks at, on the ground. The whole map fits in a circle of radius 1 around the point 0, 0. On the flat map, `tx` grows to the right and `ty` grows upwards. |
| `tz` | The height of that point above the ground, in the unit of the map. The summit is at 0.55 in the mountain view. |
| `d` | The distance from the point to the camera, in the unit of the map. The whole landscape fits at about 3. |
| `az` | The side on which the camera stands, as an angle in radians around the point. At 0 the camera stands on the side where `tx` grows, and the angle grows anticlockwise seen from above. |
| `pol` | The tilt in radians, from 0 for straight down to 1.57 for level with the ground. |
| `zs` | How far the modules are raised, from 0 on the flat map to 0.55 in the mountain view. |
| `fov` | The angle of view in degrees, from the lower edge of the frame to the upper edge. Both views use 35, and a larger number gives a wider view. |

A pose step can give any of the eight numbers. A number that it leaves out keeps its value from
the end of the step before. A `camera` field changes only the numbers it gives and leaves the
rest of its step's place as the step set it. The field `orbit`, the field `turn` of a chain step
and `fov` take degrees, while `az` and `pol` take radians.

## Chains

A chain step moves a marker, called the head, along a chain of imports, from module to module.

| `chain` | The chain |
|---|---|
| `"longest"` | One longest chain in the proof, 199 modules from the summit down to a module that imports only Mathlib. |
| `{"from": "A", "to": "B"}` | The shortest chain of imports from module A down to module B. The tour fails with a message when A does not rest on B. |
| `["A", "B", "C"]` | The listed modules, in this order. The tour draws the list as given and leaves the imports unchecked. |

| Field of a chain step | Meaning | Default |
|---|---|---|
| `hop` | Seconds from one module to the next. A chain step that covers n modules makes n − 1 hops and runs for n − 1 times `hop` seconds. | `0.3`, and `1.5` on a ride |
| `from`, `to` | The first and the last module to cover, as places in the chain counted from 0, both included. The step then covers `to` minus `from` plus 1 modules. | the whole chain |
| `ride` | `true` puts the camera on the chain, as described under the table. An object does the same and sets details of the ride. `above` is the number of levels the camera travels above the chain, `down` is the downward tilt in degrees at the height of the summit, and `fov` is the angle of view in degrees. `{"above": 20, "down": 45}` rides higher and looks further down. | seen from outside. On a ride `above` is `10`, `down` is `35` and `fov` is `70` |
| `distance` | The distance of the camera from the chain when seen from outside, in the unit of the map. | `0.7` |
| `smooth` | The camera follows the average place of the chain over this many modules either side of the head. A larger number gives a calmer camera. | `3`, and `0` on a ride |
| `turn` | Degrees per second that the camera moves around the chain when seen from outside, anticlockwise seen from above. A negative number moves it clockwise. | `3` |

The fields `from` and `to` stand on the step itself and count places. Place 0 is the first module
of the chain, which on the longest chain is the summit. Either field can stand alone. They differ
from the `from` and `to` inside `chain`, which name modules, and from the options `--from` and
`--to` of the recorder, which are seconds. A chain names its modules as a module step does, by
the full Lean name or by the last part when only one module ends with it.

On a chain step, `move` is the travel to the start of the chain and `hold` is the stay at its
end.

Seen from outside, the camera glides beside the chain. The head is a white dot. The chain behind
it is a line, bright over the last twelve modules and faint before them, and the modules that the
head has passed turn orange.

On a ride, the camera is the head. It travels along the chain, 10 levels above it, and looks the
way it travels, with an angle of view of 70 degrees. At the height of the summit it looks down by
35 degrees. The tilt shrinks evenly with the height of the chain, to 8 degrees at the ground, so
the landscape below fills the picture while the chain is high. The chain ahead is a line that
starts under the camera, with a small circle on each of the next three modules, and every module
of the chain is orange. During the last third of a hop and the first third of the next one, the
camera turns towards the new direction.

Every hop takes the same time, whatever its length on the map. A chain that jumps from one
folder to a distant one therefore crosses the map fast on that hop. On a ride, set `hop` to one
second or more so that a viewer can follow each turn. Ride a part of a chain, chosen with `from`
and `to`, because a ride down the whole longest chain at the default `hop` lasts 297 seconds.

## Writing a tour

1. Serve the folder and open the page, as the section Seeing a tour in the page describes.
2. Create a file in `verification/explorer/tours/` with the ending `.json` and the outer shape of
   the example, with an empty list of steps.
3. Move the camera to a picture that the clip should show, and press Copy camera. Paste the pose
   step into the list and set its `move` and `hold`. Give the first step of the file `"move": 0`.
4. Add the steps between the poses, such as a chain step, an orbit step, a module step or an area
   step.
5. Open the page with `?tour=` and the file's path from the served folder, such as
   `?tour=tours/my-tour.json`. Press Follow chain and watch. Drag the bar to the moments that
   need another look.
6. Record a short part first, with `--from` and `--to`, and look at the file. Then record the
   whole tour.

Shots that the edit should be able to reorder belong in tour files of their own.

## What a chain shows, for the narration

A chain here is a chain of imports between files. It says nothing about which theorem uses which
lemma, and a file can import a file whose theorems it leaves unused. That finer picture needs a
graph of which declaration uses which. The Comparator export provides such a graph, and the
explorer does not read it yet.

A theorem can use only theorems of its own file and of files that its file rests on. A chain of
theorems that use one another therefore passes through at most as many modules of the proof
below a module as the module's height, before it continues into Mathlib. The height is in this
sense an upper limit for the depth of the proof below a module, counted in the proof's own files.
The captions of a chain show a module's place in the chain and leave the height out.

## Limits of this version

- A folder name appears or disappears abruptly, without a fade, when its ring grows or shrinks
  past a fixed size on the screen. Set `"labels": false` when that disturbs a shot.
- A caption has one line, or one line each for its title and its text. A line that is too wide
  for the frame gets smaller type and then loses characters, so keep captions short.
- A caption shows names and places. The statements of a module are not available to captions
  yet.
- A ride exists for chains only.

## Adding a kind of step

`Tour.load` in `tour.js` turns each step into segments of the timeline. A segment has a kind, a
length in seconds, the camera at its start, what is lit, the caption, the dimming and the largest
dot. `Tour.seek` finds the segment of a moment and computes the camera from the segment's kind. A
new kind of step needs a branch in both functions.

`Tour.seek` has to stay a function of the moment alone. Everything on the screen must follow from
`t` and the loaded tour, because the recorder asks for frames one by one and the bar of the page
jumps to any moment. A step that needs data from the network loads it before the tour starts.

`mountain.js` gives tours these functions on `window.Mountain`:

| Function | Use |
|---|---|
| `getPose()`, `setPose(pose)` | Read and set the camera numbers. `setPose` changes the numbers it is given. |
| `home("mountain")`, `home("map")` | The pose that shows the whole landscape. |
| `at(id)` | The place of a module, as x, y and height. |
| `areaPlace(index)` | The centre of a folder, its median height and the distance at which it fills the frame. |
| `selectModule(id, false, true)`, `selectArea(index, false, true)`, `clear(true)` | Light a module or a folder, or nothing. The argument `false` keeps the camera where it is, and the argument `true` leaves the panels of the page alone. |
| `mark(ids, count)` | Turn the first `count` modules of a list orange. |
| `path(a, b)` | The shortest chain of imports from module a down to module b. |
| `trail`, `caption`, `dimming`, `maxDot`, `showLabels` | Values that the overlay and the dots read on every frame. |
| `grab()` | Draw now and return the frame as pixels. |

A module's `id` is its number in the explorer's data, and a folder's `index` is its number in
the list of folders. The page turns names into these numbers with the functions `module(name)`
and `area(name)` of the object `look` in `index.html`, which it passes to `Tour.load`.
