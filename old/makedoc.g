##
##  this creates the documentation, needs: GAPDoc package, latex, pdflatex,
##  mkindex, dvips
##  
##  Copyright (C) 2006  Max Neunhoeffer, Lehrstuhl D f. Math., RWTH Aachen
##  This file is free software, see license information at the end.
##  

LoadPackage("GAPDoc");

lib:= "../lib/";
files:= [ 
          "methods.g", "iterator.g", "walker.g",
          "subsets.g", "towers.g", "classes.g",
          "shapes.g", "alleys.g", "streets.g",
          "descent.g", "category.g", "groupoid.g",
          ];
files:= List(files, x-> Concatenation(lib, x));
MakeGAPDocDoc("doc", "zigzag", files, "ZigZag");

GAPDocManualLab("ZigZag");

quit;

##
##  This program is free software; you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation; version 2 of the License.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program; if not, write to the Free Software
##  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
##
