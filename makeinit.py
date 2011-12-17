##
##  $Id: makeinit.py,v 1.2 2007/10/15 08:56:12 goetz Exp $
##

init = open("init.g")
out = open("init.new", 'w')
line = init.readline()
while not line.startswith('AUTO'):
    print >> out, line[:-1]
    line = init.readline()
    
import glob, re
funcs = {}
for name in glob.glob("lib/*.g"):
    text = open(name)
    list = 'AUTO( ReadPkg( "zigzag", "%s", "%s" )' %  (name[:3], name[4:-2])
    for line in text:
        m = re.match('(^[a-zA-z0-9_]+ *):=', line)
        if m:
            f = m.group(1)
            if f in funcs:
                print "clash %s in %s and %s" % (f, funcs[f], name)
            funcs[f] = name
            if len(list + ', ' + f) < 78:
                list += ', ' + f
            else:
                print >> out, list + ','
                list = '  ' + f
    print >> out, list + ');\n'
