#!/bin/bash
# $Id: check3.sh,v 1.3 2013-04-16 14:06:38 deraugla Exp $

../puiseux -f test3.in -d | diff test3.out -
