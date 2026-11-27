#!/usr/bin/env python3
"""Check a finite certificate proving the stated result for ALL even n>10000.

Run with ordinary Python 3, without -O. No third-party packages are needed.
The checks use affine integer expressions on an entire infinite half-line;
they do not enumerate a finite range of orders.
"""
import json
from pathlib import Path

if not __debug__:
    raise SystemExit("Verification uses assertions. Run Python without -O or -OO.")

import verify_g_certificate
import verify_h_odd_certificate
import verify_h_even_certificate

ROOT = Path(__file__).resolve().parent

def main():
    print("G_n (n = 2 mod 4)", flush=True)
    verify_g_certificate.verify(json.loads((ROOT / "g_all_certificate.json").read_text()))
    print("H_n (n = 4 mod 8)", flush=True)
    verify_h_odd_certificate.verify(ROOT / "h_odd_certificate.json")
    print("H_n (n = 0 mod 8)", flush=True)
    verify_h_even_certificate.verify(json.loads((ROOT / "h_even_certificate.json").read_text()))
    print("PASS: every even n > 10000 is covered; every cell is avoided by a transversal.")

if __name__ == "__main__":
    main()
