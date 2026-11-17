# campaign launcher
import os
from pathlib import Path
import sys


if __name__ == '__main__':
    runner = Path(__file__).resolve().parent / 'solver/run_campaign.py'
    os.execv(sys.executable, [sys.executable, str(runner), *sys.argv[1:]])
