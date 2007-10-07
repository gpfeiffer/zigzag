#############################################################################
##
#A  $Id: init.g,v 1.20 2007/10/07 23:20:06 goetz Exp $
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2001-2007, Götz Pfeiffer
##
##  This is the init file of the ZigZag package.
##

#############################################################################
ZIGZAG:= rec();
ZIGZAG.Version:= "0.71";
ZIGZAG.Date:= "09-07-2007";

#############################################################################
##
#R  RequirePackage . . . . . . . . . . . . . . . . . . . . . . . . . require.
##
##  Here is the list of packages  which this package needs as prerequisites.
##
RequirePackage("monoid");
RequirePackage("chevie");

#############################################################################
##
#F  InfoZigzag? . . . . . . . . . . . . . . . . . . . . . . . info functions.
##
if not IsBound(InfoZigzag1) then InfoZigzag1:= Ignore; fi;
if not IsBound(InfoZigzag2) then InfoZigzag2:= Ignore; fi;

#############################################################################
##
#A  AUTO . . . . . . . . . . . . . . . . . . . . . . . . . . . .  auto reads.  
##
AUTO( ReadPkg( "zigzag", "lib", "alleys" ),
  HeadAlley, TailAlley, OnAlleys, DeltaAlley, LittleDeltaAlley,
  BigMatrixAlley, ProductAlleys, ProductAlleyList, FactorsAlley,
  StabilizerAlley, ReversedAlley );

AUTO( ReadPkg( "zigzag", "lib", "streets" ),
  StreetOps, Street, IsStreet, Streets0, Streets, NrStreets,
  EssentialStreets, ProductAlleyMatrices, ProductAlleyMatrixList,
  SumAlleyMatrices, DeltaPath, Negative, DeltaPath,
  QuiverRelations0, QuiverRelations, StreetProduct, PrintQuiver,
  DimensionsMatrix, VerifyQuiver );

AUTO( ReadPkg( "zigzag", "lib", "iterator" ),
  IteratorSet, Iterator, IteratorRange );

AUTO( ReadPkg( "zigzag", "lib", "methods" ),
  Call, ApplyMethod, PartitionOps, Partition );

AUTO( ReadPkg( "zigzag", "lib", "shapes" ),
  ShapeOps, Shape, IsShape, NormalizerComplement, ShapesRank,
  Shapes, SubsetsShapes, ComplementsShapes, IncidenceMatShapes,
  CollapsedIncMatShapes, IncMatShapes, FusMatShapes1, FusMatShapes,
  CollapsedFusMatShapes, XCharacters, ParabolicTom, YCharacters,
  ZCharacters, InvolutionShapes, Involutions, SpecialInvolutions,
      OrlikSolomonCharacter, PrimeShapes, NamesShapes, MatrixPath );

AUTO( ReadPkg( "zigzag", "lib", "category" ),
      CategoryOps, Category, CategoryEltOps, CategoryElt );

AUTO( ReadPkg( "zigzag", "lib", "groupoid" ),
      GroupoidOps, Groupoid, GroupoidEltOps, GroupoidElt );

AUTO( ReadPkg( "zigzag", "lib", "subsets" ),
  PrefixesOps, Prefixes, IsPrefixes, WeakIntervalOps, WeakInterval,
  IsWeakInterval, ParabolicTransversalOps, ParabolicTransversal,
  IsParabolicTransversal, DescentClassOps, DescentClass,
  IsDescentClass, DescentClasses, LeftParabolicTransversalOps,
  LeftParabolicTransversal, IsLeftParabolicTransversal,
  DoubleParabolicTransversalOps, DoubleParabolicTransversal,
  PDTransversalOps, PDTransversal, XJKLOps, XJKL, IsXJKL );

AUTO( ReadPkg( "zigzag", "lib", "walker" ),
  BreadthFirst, PreOrder, NrPreOrder, PreOrderProperty,
  NrPreOrderProperty, PostOrder, PostOrderProperty,
  NrPostOrderProperty, BinomialTreeOps, BinomialTree );

AUTO( ReadPkg( "zigzag", "lib", "zigzag" ),
  DescentAlgebraOps, DescentAlgebra, IsDescentAlgebra,
  CharacterDescentElt, SlowFoundation, SlowI, SlowCombine,
  MaximalAJKL1, MaximalAJKL2, MaximalAJKL, MatCompressedAJKL,
  ProductCompressedAJKL, RightRegularX, LeftRegularX, LeftRegularY,
  LeftRegularZ, LeftRegularE, DiagonalMat,
  SizesDescentConjugacyClasses, ECharacters, CCharacters,
  WhatCharacters, PrimitiveIdempotents, CartanMatDescent, HomDescent,
  RadicalDescent, RadicalSeriesDescent, MatsRadsDescent,
  ProjectiveModule, LaTeXProjectiveModule, MatDescentVec,
  MatQuiverSym, MajorIndex, RanMatDescent, SizMatDescent,
  LisMatDescent, ClosLis, OpenLis, ClosLisRank, OpenLisRank, Lat,
  RightIdeal, LeftIdeal, RightPIE, SetComposition, IsNonZero );

# print welcome message.
if BANNER then
    Print("ZigZag Version ", ZIGZAG.Version, " (", ZIGZAG.Date, ").\n");
fi;
