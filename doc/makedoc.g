path:= Directory("/home/goetz/text/descent/zigzag/doc");
main:= "zigzag.xml";
files:= [];
bookname:= "ZigZag";
str:= ComposedXMLString(path, main, files);
r:= ParseTreeXMLString(str);
CheckAndCleanUpGapDocTree(r);
l:= GAPDoc2LaTeX(r);;
