path:= Directory("/home/goetz/text/descent/zigzag/doc");
main:= "zigzag.xml";
files:= [ "../shapes.g", "../iterator.g" ];
bookname:= "ZigZag";
str:= ComposedXMLString(path, main, files);
r:= ParseTreeXMLString(str);
CheckAndCleanGapDocTree(r);
l:= GAPDoc2LaTeX(r);;
FileString(Filename(path, Concatenation(bookname, ".tex")), l);
