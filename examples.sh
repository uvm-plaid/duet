#!/bin/bash

for e in gd-pb.ed.duet bolt-on.ed.duet fw.ed.duet gd-pb-mini.ed.duet parallel-privacy.ed.duet gd-unbounded-pb.ed.duet hyperparam.ed.duet adaptive-clip.ed.duet normalize.ed.duet; do
    echo "================================================================================"
    echo "Running example:" $e
    echo "================================================================================"
    stack run -- check examples/${e}
done
