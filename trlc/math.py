#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2022 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
#
# This file is part of the TRLC Python Reference Implementation.
#
# TRLC is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# TRLC is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with TRLC. If not, see <https://www.gnu.org/licenses/>.

from fractions import Fraction
from math import floor, ceil


def remainder(lhs, rhs):
    assert isinstance(lhs, int)
    assert isinstance(rhs, int)

    mod = abs(lhs) % abs(rhs)

    if lhs >= 0:
        return mod
    else:
        return -mod


def round_nearest_away(value):
    assert isinstance(value, Fraction)

    if value >= Fraction(0):
        return floor(value + Fraction(1, 2))
    else:
        return ceil(value - Fraction(1, 2))
