class
	PERIMETER_DRIVER_7

feature

	driver (a_select, a_w, a_x, a_y, a_z, a_short, a_long: INTEGER): INTEGER
		require
			a_select_in_bounds: 0 <= a_select and a_select < 6
			side_pos: 0 < a_w and 0 < a_x and 0 < a_y and 0 < a_z and 0 < a_short and 0 < a_long
		local
			p: PERIMETER
		do
			create p
			inspect a_select
				when 0 then
					Result := p.square (a_short)
				when 1 then
					Result := p.pentagon (a_w)
				when 2 then
					Result := p.hexagon (a_long)
				when 3 then
					Result := p.rectangle (a_w, a_x)
				when 4 then
					Result := p.triangle (a_w, a_x, a_y)
				when 5 then
					Result := p.trapezium (a_w, a_x, a_y, a_z)
			end

		ensure
			square: (a_select = 0 and 0 < a_short) implies (Result = 4 * a_short)
			pentagon: (a_select = 1 and 0 < a_w) implies (Result = 5 * a_w)
			hexagon: (a_select = 2 and 0 < a_long) implies (Result = 6 * a_long)
			rectangle: (a_select = 3 and 0 < a_w and 0 < a_x) implies (Result = 2 * a_w + 2 * a_x)
			triangle: (a_select = 4 and 0 < a_w and 0 < a_x and 0 < a_y) implies (Result = a_w + a_x + a_y)
			trapezium: (a_select = 5 and 0 < a_w and 0 < a_x and 0 < a_y and 0 < a_z) implies (Result = a_w + a_x + a_y + a_z)
		end
end
