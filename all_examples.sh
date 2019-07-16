#!/bin/bash
FILES=examples/complete/*.duet
for e in $FILES
do
  echo "================================================================================"
  echo "Running example:" $e
  echo "================================================================================"
  stack run -- check $e
done
