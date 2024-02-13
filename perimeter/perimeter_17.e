class
	PERIMETER_17

feature

	square (a_x: INTEGER): INTEGER
		require
			side_pos: a_x > 0
		local
			square_perimeter: INTEGER
		do
			square_perimeter := 4 * a_x
			Result := square_perimeter
		ensure
			res_perimeter_square: Result = 4 * a_x
		end

	pentagon (a_x: INTEGER): INTEGER
		require
			side_pos: a_x > 0
		local
			pentagon_perimeter: INTEGER
		do
			pentagon_perimeter := 5 * a_x
			Result := pentagon_perimeter
		ensure
			res_perimeter_pentagon: Result = 5 * a_x
		end

	hexagon (a_x: INTEGER): INTEGER
		require
			side_pos: a_x > 0
		local
			hexagon_perimeter: INTEGER
		do
			hexagon_perimeter := 6 * a_x
			Result := hexagon_perimeter
		ensure
			res_perimeter_hexagon: Result = 6 * a_x
		end

	rectangle (a_x, a_y: INTEGER): INTEGER
		require
			side_pos: a_x > 0 and a_y > 0
		local
			perimeter_rectangle: INTEGER
		do
			perimeter_rectangle := 2 * (a_x + a_y)
			Result := perimeter_rectangle
		ensure
			res_perimeter_rectangle: Result = 2 * a_x + 2 * a_y
		end

	triangle (a_x, a_y, a_z: INTEGER): INTEGER
		require
			side_pos: a_x > 0 and a_y > 0 and a_z > 0
		local
			triangle_perimeter: INTEGER
		do
			triangle_perimeter := a_x + a_y + a_z
			Result := triangle_perimeter
		ensure
			res_perimeter_triangle: Result = a_x + a_y + a_z
		end

	trapezium (a_w, a_x, a_y, a_z: INTEGER): INTEGER
		require
			side_pos: a_w > 0 and a_x > 0 and a_y > 0 and a_z > 0
		local
			trapezium_perimeter: INTEGER
		do
			trapezium_perimeter := a_w + a_x + a_y + a_z
			Result := trapezium_perimeter
		ensure
			res_perimeter_trapezium: Result = a_w + a_x + a_y + a_z
		end
end
