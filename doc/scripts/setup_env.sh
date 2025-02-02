#!/bin/sh

# Set up a new or existing .venv directory as a Python virtual environment
# suitable for building SAW documentation, particularly with make_docs.sh.

REQUIREMENTS="$(dirname $0)/requirements.txt"

echo "Checking for python3..."
if ! [ -x "$(command -v python3)" ];
then
    echo "Error: python3 is not installed." >&2
    return 1
fi

if [ -d ".venv" ];
then
    echo "Found a '.venv' directory."

    if ! [ -e .venv/bin/activate ]
    then
        echo -e "\033[1;33mWARNING:\033[0m '.venv/bin/activate' not found."
        echo "Running python3 -m venv .venv to repair..."
        python3 -m venv .venv
    fi

    # We want to check _the virtual environment's_ pip list, so activate here.
    . .venv/bin/activate

    if pip freeze -r "${REQUIREMENTS}" 2>&1 | grep -q "not installed"
    then
        echo -e "\033[1;33mWARNING:\033[0m 'requirements.txt' not satisfied."
        echo "Installing dependencies..."
        pip install -qr "${REQUIREMENTS}"
    fi

    echo -e "\033[1;32mEnvironment updated successfully!\033[0m"
    exit
fi

echo "No '.venv' directory found."
echo "Running python3 -m venv .venv..."
python3 -m venv .venv

. .venv/bin/activate

echo "Installing dependencies..."
pip install -qr "${REQUIREMENTS}"

echo -e "\033[1;32mEnvironment created successfully!\033[0m"
