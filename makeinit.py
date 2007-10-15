## gawk 'BEGIN {                                                              \
##     while ( getline < "lib/init.g" && $0 !~ /^AUTO/ )                      \
##         print $0;                                                          \
## }                                                                          \
##                                                                            \
## FNR == 1 {                                                                 \
##     if ( line != "" && line !~ /^AUTO/ )                                   \
##         print line " );\n";                                                \
##     line = "AUTO( ReadPkg(\"zigzag\",\"lib\", ";                           \
##     line = line "\"" substr( FILENAME, 5, index(FILENAME,".")-5 ) "\" )";  \
## }                                                                          \
##                                                                            \
## /^[A-Za-z0-9_]+ *:=/ && FILENAME != "lib/init.g" {                         \
##     if ( $1 in funcs )                                                     \
##         print "clash " $1 " in " funcs[$1] " and " FILENAME > "/dev/stderr";\
##     funcs[$1] = FILENAME;                                                  \
##     if ( length( line ", " $1 ) <= 77 && line !~ /^AUTO/ ) {               \
##         line = line ", " $1;                                               \
##     }                                                                      \
##     else {                                                                 \
##         print line ",";                                                    \
##         line = "  " $1;                                                    \
##     }                                                                      \
## }                                                                          \
##                                                                            \
## END {                                                                      \
##     if ( line != "" && line !~ /^AUTO/ )                                   \
##         print line " );\n";                                                \
## }' lib/*.g > lib/init.new
## mv lib/init.g lib/init.g~
## mv lib/init.new lib/init.g
## diff -u lib/init.g~ lib/init.g

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
    list = 'AUTO( ReadPkg( "zigzag", "lib", "%s" )' %  name[4:-2]
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
