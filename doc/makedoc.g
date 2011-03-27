path:= Directory("/home/goetz/projects/zigzag/doc");
main:= "zigzag.xml";
lib:= "../lib/";
files:= [ 
          "methods.g", "iterator.g", "walker.g",
          "subsets.g", "skyline.g", "classes.g",
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

MakeGAPDocDoc(path, main, files, bookname);
#MakeGAPDocDoc(path, main, files, bookname, "MathML");
