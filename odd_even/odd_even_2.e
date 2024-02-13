class
	ODD_EVEN_2

feature

	is_even (a_x: INTEGER): BOOLEAN
		do
			Result := (a_x \\ 2 /= 0) -- Result := (a_x \\ 2 = 0)
		ensure
			res_of_a_x_even: Result = (a_x \\ 2 = 0)
			res_of_a_x_odd: (not Result) = (a_x \\ 2 /= 0)
		end

	is_odd (a_x: INTEGER): BOOLEAN
		do
			Result := (a_x \\ 2 /= 0)
		ensure
			res_of_a_x_even: (not Result) = (a_x \\ 2 = 0)
			res_of_a_x_odd: Result = (a_x \\ 2 /= 0)
		end

end
