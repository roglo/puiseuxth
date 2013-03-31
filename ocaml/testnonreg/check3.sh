#!/bin/bash
# $Id: check3.sh,v 1.2 2013-03-31 07:59:59 deraugla Exp $

../puiseux -f test3.in | diff test3.out -
