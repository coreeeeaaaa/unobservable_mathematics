#!/usr/bin/env python3
import os
import subprocess

def rewrite_commit_messages():
    # Get all commit hashes
    result = subprocess.run(['git', 'log', '--format=%H'], capture_output=True, text=True)
    commits = result.stdout.strip().split('\n')

    print(f"Found {len(commits)} commits to rewrite")

    # Use git filter-repo with simpler approach
    cmd = [
        'git', 'filter-repo', '--force',
        '--msg-filter', 'echo "chore: repository update"'
    ]

    try:
        subprocess.run(cmd, check=True)
        print("Successfully rewrote all commit messages")
    except subprocess.CalledProcessError as e:
        print(f"Error: {e}")
        return False

    return True

if __name__ == "__main__":
    rewrite_commit_messages()