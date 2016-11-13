#!/bin/bash

mkdir bin
cd core
make r 2>&1
cp treeRat_release ../bin/treeRat

