#!/usr/bin/env python3
"""Use the existing lookup capture with its full-coverage option enabled.

The original CLI does not expose this helper option. Capturing the entire
allocation lets the theorem's mapping predicate inspect original bytes,
without changing the captured capacity word or filling absent memory.
Arguments are exactly those of binary/capture_lookup.py.
"""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import capture_lookup

original_capture = capture_lookup.capture


def capture_full(*args, **kwargs):
    kwargs["full_coverage"] = True
    return original_capture(*args, **kwargs)


capture_lookup.capture = capture_full

if __name__ == "__main__":
    capture_lookup.main()
