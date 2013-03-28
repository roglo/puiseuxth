#!/bin/bash
# $Id: show.sh,v 1.1 2013-03-28 13:24:20 deraugla Exp $

arg=

function check
{
    echo "\$ ./puiseux$arg '$1'"
    ../puiseux$arg --with-sqrt-x "$1" -v -n 1 2>&1
    echo
}

check '(-x3+x4)-2x2y-xy2+2xy4+y5'
check 'x4-x3y+3x2y3-3xy5+y7'
check '2x5-x3y+2x2y2-xy3+2y5'
check '(x2+4x3+6x4)-4x4y+(-2x-4x2-2x3)y2+y4'

arg=" -y X"
check 't2X6+6t2X5+(8t3-2t2+t)X3+(7t4-t2-2t)X2+(8t3-3t)X-t8+t3'
arg=

check 'y5-4y4+4y3+2x2y2-xy2+2x2y+2xy+x4+x3'
check 'y2-x3+2x2-x'

check '2x5-x3y+2x2y2-xy3+2y5'
check 'y4-(2x3+2x2)y2+(x6+2x5+x4)'
check 'y4-2x3y2-2x2y2+x6+2x5+x4'
check ' -x3+x4-2x2y-xy2+2xy4+y5'
check 'x2+xy+y2+x+y'			#1
check 'x2+xy+y2+y'
check 'x2+xy+y2+x'
check 'x2+4xy+y2'
check 'x2+xy+y2'			#5
check 'x2+2xy+y2'
check 'x3+x2y+xy2+y3+x2+xy+y2+x+y'
check 'x3+x2y+xy2+y3+x2+xy+y2+y'
check 'x3+x2y+xy2+y3+x2+xy+y2+x'
check 'x3+x2y+xy2+y3+x2'		#10
check 'x3+x2y+xy2+y3+y2'
check 'x3+x2y+xy2+y3+x2+xy'
check 'x3+x2y+xy2+y3+xy+y2'
check 'x3+x2y+xy2+y3+xy'
check 'x3+x2y+xy2+y3+xy+y'		#15
check 'x3+x2y+xy2+y3+xy+x'
check 'yx2-y3'
check 'x3+x2y+xy2+y3'
check 'yx2-2xy2+y3'
check 'x3-3yx2+3xy2-y3'			#20
check 'x3+x2y+xy2+y3+x2+4xy+y2'
check 'x3+x2y+xy2+y3+x2+xy+y2'
check 'x3+x2y+xy2+y3+x2+2xy+y2'
check 'x3+x2y+xy2+y3+x2+4xy+4y2'
check 'x4+x3y+x2y2+xy3+y4+x+y'		#25
check 'x4+x3y+x2y2+xy3+y4+x2+y'
check 'x4+x3y+x2y2+xy3+y4+x+y2'
check 'x4+x3y+x2y2+xy3+y4+x3+y'
check 'x4+x3y+x2y2+xy3+y4+y3+x'
check 'x4+x3y+x2y2+xy3+y4+y3+x2'	#30
