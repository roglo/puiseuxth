#!/bin/sh
# $Id: check.sh,v 1.4 2013-04-10 09:22:09 deraugla Exp $

echo "check1..."
./check1.sh &
echo "check2..."
./check2.sh &
echo "check3..."
./check3.sh &
echo "check4..."
./check4.sh &
echo "check5..."
./check5.sh
