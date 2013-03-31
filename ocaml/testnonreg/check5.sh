#!/bin/bash
# $Id: check5.sh,v 1.2 2013-03-31 07:59:59 deraugla Exp $

../puiseux -f test3.in -e 0 | diff test5.out -
