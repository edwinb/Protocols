#!/bin/bash

if [[ $# -eq 0 ]];
then
    IDRIS=idris
    echo "Using system installed Idris"
else
    IDRIS=$1
    echo "Using user supplied Idris"
fi

die() {
	echo "$1" >&2
	exit 1
}

make clean

echo "Compiling Working Tests"
make IDRIS=$IDRIS working || die "* could not compile UtilServer.idr *"

echo "Finshed compilation."

echo "Telling lame joke..."
gtimeout 3s ./knock > output || die "* test failed or timed out *"

echo "Performing Handshake"
gtimeout 3s ./shake >> output || die " * test failed or timed out *"

echo "Compiling Failing test"
make IDRIS=$IDRIS fail >> output

if diff output expected; then
	echo "### everything PASS ###"
	make clean
	exit 0
else
	echo "### something FAIL ###"
	make clean
	exit 1
fi
