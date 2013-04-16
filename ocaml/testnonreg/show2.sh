#!/bin/bash
# $Id: show2.sh,v 1.3 2013-04-16 14:06:38 deraugla Exp $

arg=

function check
{
    echo "\$ ./puiseux$arg '$1'"
    ../puiseux$arg "$1" -d 2>&1
    echo
}

. common.sh
