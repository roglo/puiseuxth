#!/bin/bash
# $Id: check5.sh,v 1.3 2013-04-16 14:06:38 deraugla Exp $

../puiseux -f test3.in -e 0 -d | diff test5.out -
