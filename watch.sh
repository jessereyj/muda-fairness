#!/usr/bin/env bash
set -euo pipefail

echo "Watching for changes..."
echo "Press Ctrl+C to stop"
echo ""

if ! command -v inotifywait &> /dev/null && ! command -v fswatch &> /dev/null; then
    echo "Error: Neither inotifywait nor fswatch found."
    echo "Install one of:"
    echo "  - Linux: apt-get install inotify-tools"
    echo "  - macOS: brew install fswatch"
    exit 1
fi

build_project() {
    clear
    echo "Change detected, rebuilding..."
    ./build.sh
}

# Initial build
build_project

# Watch for changes
if command -v fswatch &> /dev/null; then
    # macOS
    fswatch -o LTL MUDA Fairness | while read; do
        build_project
    done
else
    # Linux
    while inotifywait -r -e modify,create,delete LTL/ MUDA/ Fairness/; do
        build_project
    done
fi