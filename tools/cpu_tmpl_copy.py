#!/usr/bin/env python3
"""Copy a hand-written module template verbatim (route driver stage for modules that are template-source files).  llm_written."""
import argparse, shutil
ap = argparse.ArgumentParser(); ap.add_argument('--src', required=True); ap.add_argument('--out', required=True); a = ap.parse_args()
shutil.copyfile(a.src, a.out)
