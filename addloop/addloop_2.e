class
	ADDLOOP_2

feature
	add_loop (x, y: INTEGER): INTEGER
		require
			sum_no_underflow: {INTEGER}.min_value <= x + y
			sum_no_overflow: x + y <= {INTEGER}.max_value
			y_not_min: y /= {INTEGER}.min_value
		local
			sum, n: INTEGER
		do
			sum := x
			if y > 0 then
				n := y
				from
				invariant
					add_partial_sum_correct: sum = x + y - n
					non_non_negative: 0 <= n
				until
					not (n >= 0)
				loop
					sum := sum + 1
					n := n - 1
				variant
					n
				end
			else
				n := - y
				from
				invariant
					subtract_sum_correct: sum = x + y + n
					non_non_negative2: 0 <= n
				until
					not (n > 0)
				loop
					sum := sum - 1
					n := n - 1
				variant
					n
				end
			end
			Result := sum
		ensure
			result_is_sum: Result = x + y
		end

end
