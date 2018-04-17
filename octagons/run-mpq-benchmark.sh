#!/bin/bash

export LD_LIBRARY_PATH=.:../apron

./octbenchMPQ meet &> meet$1
./octbenchMPQ join &> join$1
./octbenchMPQ lincons &> lincons$1
