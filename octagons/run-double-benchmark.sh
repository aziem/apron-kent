#!/bin/bash

export LD_LIBRARY_PATH=.:../apron

./octbenchD meet &> meet$1
./octbenchD join &> join$1
./octbenchD lincons &> lincons$1
