path:= Directory("/home/goetz/text/descent/zigzag/doc");
main:= "zigzag.xml";
lib:= "../lib/";
files:= [ 
          "methods.g", "iterator.g", "walker.g",
          "subsets.g", "shapes.g", "alleys.g", "streets.g",
          "zigzag.g",
        ];
files:= List(files, x-> Concatenation(lib, x));
bookname:= "zigzag";
str:= ComposedXMLString(path, main, files);
r:= ParseTreeXMLString(str);
CheckAndCleanGapDocTree(r);
l:= GAPDoc2LaTeX(r);;
FileString(Filename(path, Concatenation(bookname, ".tex")), l);
