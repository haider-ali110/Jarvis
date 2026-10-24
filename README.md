# J.A.R.V.I.S.

A voice and text assistant for your PC with a 3D hologram interface.
`app.py` is the brain (Python, Flask, speech, system control). `index.html` is the face (three.js).

Built for Fedora Linux. Windows has partial support.
   [Full feature guide](https://haider-ali110.github.io/Jarvis/)

## Features

- **3D interface:** spinning core, watching eye, floating gauges and panels, evil cursor with bat trail, seasons (snow, rain, embers, leaves), bat intro.
- **Customize panel:** colours, 6 themes, core shape, effects, camera, every panel's position and size, quick commands. Everything is saved and restored on restart.
- **Voice and text:** talk or type. Spoken replies in several voices (evil, robot, normal, friday, hacker).
- **Speech recognition:** Whisper (offline, best with accents), Google, or Vosk (offline). English only.
- **Transform modes:** jarvis, normal, evil, friday, hacker, robot. Each changes the voice and personality.
- **Password lock:** lock Jarvis and the screen, unlock by saying or typing the password. Wrong tries cause a short lockout.
- **System control:** volume, brightness, Wi-Fi, Bluetooth, media keys, screenshots, clipboard, voice typing, window control, open and close apps.
- **Safe file commands:** create, read, rename, move, copy, find and trash files in Desktop, Documents and Downloads only.
- **Productivity:** to do list, notes, timers, reminders, stopwatch, focus timer, daily briefing.
- **Lookups:** weather, news, Wikipedia, dictionary, unit converter, web and YouTube search, AI questions.
- **Fun:** voice math, jokes, coin, dice, random numbers.
- **Smart understanding:** fixes mis-heard words, understands rough English, asks before doing anything unsure.
- **Safety:** shutdown, restart, kill and delete always ask yes or no first.

## Example commands

```
open firefox
increase the volume
set brightness to 70 percent
take a screenshot
what is the weather
set a timer for 10 minutes
add task buy milk
create file notes dot txt with hello in documents
what is 25 times 4
convert 10 km to miles
transform into evil
change theme to blue
lock jarvis
```

Say `what can you do` to hear the full list.

## Install

1. Clone the repo:
   ```bash
   git clone https://github.com/haider-ali110/Jarvis.git
   cd Jarvis
   ```
2. Make a virtual environment and install the packages:
   ```bash
   python3 -m venv venv
   source venv/bin/activate
   pip install -r requirements.txt
   ```
   If `requirements.txt` is missing something, these are the packages the code uses:
   ```bash
   pip install flask flask-cors psutil requests SpeechRecognition pyaudio pywebview piper-tts faster-whisper numpy vosk
   ```
3. Install the system tools (Fedora):
   ```bash
   sudo dnf install wireplumber brightnessctl playerctl NetworkManager bluez gnome-screenshot wl-clipboard ydotool sox pipewire-utils xdg-utils glib2 espeak-ng portaudio-devel
   ```
4. Download the models (they are too large for GitHub):
   - **Piper voice:** download `en_US-ryan-high.onnx` and its `.json` from the [Piper voices](https://huggingface.co/rhasspy/piper-voices) page and put both in `~/piper-voices/`.
   - **Vosk model (optional, offline backup):** download an English model from [alphacephei.com/vosk/models](https://alphacephei.com/vosk/models) and unpack it to `~/vosk-model`.
   - **Whisper:** the model downloads itself the first time it runs.
5. Start Jarvis:
   ```bash
   python app.py
   ```
   Add `--browser` to open it in your normal browser instead of the desktop window.

Run the command `run diagnostics` to see which tools are missing.

## Password

The lock password is set in `app.py` on the line `JARVIS_PASSWORD = ...`. Change it there and restart Jarvis. The saved copy in `~/.jarvis/lock.json` is only a salted hash.

Say or type `save password` to re-save the password from the code. Commands like `set password ...` are blocked unless you set `ALLOW_PASSWORD_CHANGE_BY_COMMAND = True`.

## Settings (environment variables)

| Variable | Meaning |
|---|---|
| `JARVIS_WAKE=1` | Require "Hey Jarvis" before commands |
| `JARVIS_CITY` | Default city for weather |
| `JARVIS_STT` | `auto`, `whisper`, `google` or `vosk` |
| `JARVIS_WHISPER_MODEL` | `tiny.en`, `base.en`, `small.en`, `medium.en` |
| `JARVIS_WHISPER_DEVICE` | `cpu` or `cuda` |
| `JARVIS_LANG` | `en-IN`, `en-US`, `en-GB` |
| `JARVIS_MIC` | Microphone number (say "list microphones") |
| `JARVIS_SPEAK_TYPED=0` | Keep typed replies silent |
| `JARVIS_AI_FIX=0` | Turn off AI sentence repair |
| `JARVIS_RESTORE_MIC=0` | Do not reopen the mic on start |
| `OLLAMA_URL`, `OLLAMA_MODEL` | Local AI brain (default llama3.2) |
| `ANTHROPIC_API_KEY` | Use Claude as a backup AI brain |

## Where your data lives

Everything is stored in `~/.jarvis`: settings, theme, mode, voice, chat history, notes, tasks, aliases, custom commands and the password hash. It is never uploaded.

## Keyboard shortcuts

`V` mic on or off, `M` minimize, `H` hide the dock, `Ctrl+,` customize panel, `Ctrl+K` focus the command box, `Esc` close the panel.

## License

MIT. See [LICENSE](LICENSE).
