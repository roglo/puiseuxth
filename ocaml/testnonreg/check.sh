#!/bin/bash
# $Id: check.sh,v 1.1 2013-03-28 13:24:20 deraugla Exp $

./show.sh | diff test.out -
