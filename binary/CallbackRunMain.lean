import CallbackRun

def main : IO UInt32 := do
  match Binary.Callback.suite with
  | .ok report => IO.println report.compress; return 0
  | .error error => IO.eprintln s!"FAIL: {error}"; return 1
