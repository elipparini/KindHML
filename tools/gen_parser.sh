#!/bin/sh
# Regenerate the ANTLR parser. Requires Java 11+ and tools/antlr-4.13.2-complete.jar
# (https://www.antlr.org/download/antlr-4.13.2-complete.jar).
set -e
cd "$(dirname "$0")/../src/kindhml/grammar"
java -jar ../../../tools/antlr-4.13.2-complete.jar -Dlanguage=Python3 -visitor -no-listener KindHML.g4
