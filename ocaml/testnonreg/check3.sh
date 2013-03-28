#!/bin/bash
# $Id: check3.sh,v 1.1 2013-03-28 13:24:20 deraugla Exp $

../puiseux -f test3.txt | diff test3.out -
