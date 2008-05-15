LoadPackage("GAPDoc");

files:= List([ 
          "methods.g", "iterator.g", "walker.g",
          "subsets.g", "shapes.g", "alleys.g", "streets.g",
          "descent.g", "category.g", "groupoid.g",
        ], x-> Concatenation("../lib/", x));;

MakeGAPDocDoc("doc", "zigzag", files, "ZigZAG");

GAPDocManualLab("ZigZAG");

quit;

