path:= Directory("/home/goetz/Projects/zigzag/doc");
path:= Directory(".");
main:= "zigzag.xml";
lib:= "../lib/";
files:= [ 
          "methods.g", "iterator.g", "walker.g",
          "subsets.g", "skyline.g", "classes.g", "characte.g",
          "shapes.g", "alleys.g", "streets.g", "forests.g",
          "descent.g", "category.g", "groupoid.g",
          ];
files:= List(files, x-> Concatenation(lib, x));
bookname:= "zigzag";
#str:= ComposedXMLString(path, main, files);
#r:= ParseTreeXMLString(str);
#CheckAndCleanGapDocTree(r);
#l:= GAPDoc2LaTeX(r);;
#FileString(Filename(path, Concatenation(bookname, ".tex")), l);
#h:= GAPDoc2HTML(r);
##h:= GAPDoc2HTML(r, "Tth");
#GAPDoc2HTMLPrintHTMLFiles(h, path);

#MakeGAPDocDoc(path, main, files, bookname);
MakeGAPDocDoc(path, main, files, bookname, "Tth");
#MakeGAPDocDoc(path, main, files, bookname, "MathML");
#MakeGAPDocDoc(path, main, files, bookname, "MathJax");
