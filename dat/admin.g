#############################################################################
##
#A  admin.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010-2013  Götz Pfeiffer
##
##  This file contains the administrative part of ZigZag's explicit data.
##

#############################################################################
##
##  TYPES
##
##  a list of those types for which we have stored explicit data.
##
ZIGZAG.TYPES:= ["B7", "B8", "D7", "D8", "E7", "E8", "H4"];


#############################################################################
##
##  Data( W, dat )
##
##  find explicit data for W, or return false.
##
ZIGZAG.Data:= function(W, dat)
    local   name,  comp,  file;

    name:= ReflectionName(W);
    if name in ZIGZAG.TYPES then
        if not IsBound(ZIGZAG.(name)) then
            ZIGZAG.(name):= rec();
        fi;
        comp:= ZIGZAG.(name);
        file:= ConcatenationString(LOADED_PACKAGES.zigzag, "dat/", name, ".", dat);
        READ(file);
        if IsBound(comp.(dat)) then
            return comp.(dat);
        fi;
    fi;
    return false;
end;
