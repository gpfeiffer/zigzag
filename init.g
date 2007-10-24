#############################################################################
##
#A  $Id: init.g,v 1.23 2007/10/24 08:55:32 goetz Exp $
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2001-2007 Götz Pfeiffer
##
##  This is the init file of the ZigZag package.
##

#############################################################################
ZIGZAG:= rec();
ZIGZAG.Version:= "0.73";
ZIGZAG.Date:= "23-10-2007";

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
##  print welcome message.
##
if BANNER then
    Print("ZigZag Version ", ZIGZAG.Version, " (", ZIGZAG.Date, ").\n");
fi;

#############################################################################
##
#A  AUTO . . . . . . . . . . . . . . . . . . . . . . . . . . . .  auto reads.  
##
AUTO( ReadPkg( "zigzag", "lib", "iterator" ), IteratorList, IteratorEmpty,
  Iterator, IteratorRange, MPartitionsOps, MPartitions, NrMPartitions,
  PartitionsIntOps, PartitionsInt);

AUTO( ReadPkg( "zigzag", "lib", "alleys" ), ProductAlleys, ProductAlleyList,
  FactorsAlley, OnAlleys, StabilizerAlley, NrAlleys, LengthAlley, SourceAlley,
  TargetAlley, PrefixAlley, SuffixAlley, ActionAlley, LittleDeltaAlley,
  DeltaAlley, BigMatrixAlley, ReversedAlley, LittleDeltaBarAlley,
  ReducedWordAlley, AlleyAlgebraOps, AlleyAlgebra, IsAlleyAlgebra);

AUTO( ReadPkg( "zigzag", "lib", "category" ), CategoryOps, Category,
  IsCategory, CategoryEltOps, CategoryElt, IsCategoryElt);

AUTO( ReadPkg( "zigzag", "lib", "shapes" ), ShapeOps, Shape, IsShape,
  NormalizerComplement, ShapesRank, Shapes, SubsetsShapes, ComplementsShapes,
  IncidenceMatShapes, XCharacters, ParabolicTom, YCharacters, ZCharacters,
  InvolutionShapes, Involutions, SpecialInvolutions, OrlikSolomonCharacter,
  NamesShapes, LabelsShapes);

AUTO( ReadPkg( "zigzag", "lib", "methods" ), Call, ApplyMethod, PartitionOps,
  Partition);

AUTO( ReadPkg( "zigzag", "lib", "streets" ), StreetOps, Street, IsStreet,
  Streets, NrStreets, ProductStreetMatrices, ProductStreetMatrixList,
  SumStreetMatrices, DeltaPath, QuiverRelations, PrintQuiver,
  DimensionsMatrix, CartanMatQuiver, CartanMatStreets, QuiverMatStreets);

AUTO( ReadPkg( "zigzag", "lib", "walker" ), BreadthFirst,
  IteratorBreadthFirst, PreOrder, NrPreOrder, IteratorPreOrder,
  PreOrderProperty, NrPreOrderProperty, PostOrder, PostOrderProperty,
  NrPostOrderProperty, BinomialTreeOps, BinomialTree);

AUTO( ReadPkg( "zigzag", "lib", "subsets" ), IsLeftDescent, IsRightDescent,
  LongestElement, PrefixesOps, Prefixes, IsPrefixes, WeakIntervalOps,
  WeakInterval, IsWeakInterval, ParabolicTransversalOps, ParabolicTransversal,
  IsParabolicTransversal, DescentClassOps, DescentClass, IsDescentClass,
  DescentClasses, LeftParabolicTransversalOps, LeftParabolicTransversal,
  IsLeftParabolicTransversal, DoubleParabolicTransversalOps,
  DoubleParabolicTransversal, IsDoubleParabolicTransversal, XJKLOps, XJKL,
  IsXJKL);

AUTO( ReadPkg( "zigzag", "lib", "groupoid" ), GroupoidOps, Groupoid,
  IsGroupoid, GroupoidEltOps, GroupoidElt, IsGroupoidElt);

AUTO( ReadPkg( "zigzag", "lib", "zigzag" ), DescentAlgebraOps, DescentAlgebra,
  IsDescentAlgebra, DescentEltOps, DescentElt, IsDescentElt,
  CharacterDescentElt, MaximalAJKL, MatCompressedAJKL, ProductCompressedAJKL,
  RightRegularX, LeftRegularX, LeftRegularY, LeftRegularZ, LeftRegularE,
  DiagonalMat, SizesDescentConjugacyClasses, ECharacters, MatQuiverSym,
  MajorIndex, SetComposition, IsNonZero);

