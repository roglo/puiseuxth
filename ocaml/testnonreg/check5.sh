#!/bin/bash
# $Id: check5.sh,v 1.1 2013-03-31 06:16:39 deraugla Exp $

../puiseux -f test3.txt -e 0 | diff test5.out -
