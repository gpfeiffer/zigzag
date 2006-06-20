#############################################################################
##
#A  init.g                        Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This is the init file of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a
##  GAP package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: init.g,v 1.8 2006/06/20 08:26:55 goetz Exp $
##
RequirePackage("monoid");
RequirePackage("chevie");

AUTO( ReadPkg( "zigzag", "lib", "methods" ),
      Call,
      ApplyMethod );

AUTO( ReadPkg( "zigzag", "lib", "iterator" ),
      IteratorSet,
      IteratorRange,
      Iterator );

AUTO( ReadPkg( "zigzag", "lib", "shapes" ),
      ShapeOps,
      Shape,
      IsShape,
      Shapes,
      SubsetsShapes,
      ComplementsShapes,
      CollapsedIncMatShapes,
      CollapsedFusMatShapes,
      XCharacters,
      ParabolicTom,
      YCharacters,
      ZCharacters,
      InvolutionShapes,
      Involutions,
      NormalizerComplement );

AUTO( ReadPkg( "zigzag", "lib", "arrows"),
      HeadArrow,
      TailArrow,
      OnArrows,
      DeltaArrow,
      ArrowClassOps,
      ArrowClass,
      IsArrowClass,
      ArrowClasses );

AUTO( ReadPkg( "zigzag", "lib", "subsets.g" ),
      PrefixesOps,
      Prefixes,
      IsPrefixes,
      WeakIntervalOps,
      WeakInterval,
      IsWeakInterval,
      ParabolicTransversalOps,
      ParabolicTransversal,
      IsParabolicTransversal,
      DescentClassOps,
      DescentClass,
      IsDescentClass,
      LeftParabolicTransversalOps,
      LeftParabolicTransversal,
      IsLeftParabolicTransversal,
      DoubleParabolicTransversalOps,
      DoubleParabolicTransversal,
      IsDoubleParabolicTransversal,
      XJKLOps,
      XJKL,
      IsXJL );

AUTO( ReadPkg( "zigzag", "lib", "zigzag.g" ),
      InfoZigzag1,
      InfoZigzag2,
      DescentAlgebraOps,
      DescentAlgebra,
      IsDescentAlgebra,
      CharacterDescentElt,
      MaximalAJKL, 
      MatCompressedAJKL, 
      ProductCompressedAJKL,
      RightRegularX,
      LeftRegularX,
      LeftRegularY,
      LeftRegularZ,
      LeftRegularE,
      SizesDescentConjugacyClasses,
      ECharacters,
      CCharacters,
      PrimitiveIdempotents,
      CartanMatDescent,
      RightPIE,
      SetComposition,
      IsNonZero );

