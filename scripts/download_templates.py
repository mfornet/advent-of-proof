#!/usr/bin/env python3
"""Download the pinned, original Advent of Proof 2023 Lean templates."""

import json
import subprocess
from pathlib import Path
from urllib.parse import urlparse


ROOT = Path(__file__).resolve().parents[1]
TEMPLATES = ROOT / "templates"


def main() -> None:
    sources = json.loads((TEMPLATES / "sources.json").read_text())
    if [item["day"] for item in sources] != list(range(1, 25)):
        raise ValueError("Expected exactly the 24 challenge days in order")

    for source in sources:
        url = source["url"]
        parsed = urlparse(url)
        if parsed.scheme != "https" or parsed.hostname != "gist.githubusercontent.com":
            raise ValueError(f"Unexpected source URL: {url}")

        result = subprocess.run(
            ["curl", "-fsSL", "--retry", "3", "--max-time", "30", url],
            check=True,
            capture_output=True,
        )
        if not result.stdout or b"<html" in result.stdout[:200].lower():
            raise ValueError(f"Invalid Lean source for day {source['day']}")

        target = TEMPLATES / f"Problem{source['day']:02d}.lean"
        temporary = target.with_suffix(".lean.tmp")
        temporary.write_bytes(result.stdout)
        temporary.replace(target)
        print(f"{target.relative_to(ROOT)}: {len(result.stdout)} bytes")


if __name__ == "__main__":
    main()
