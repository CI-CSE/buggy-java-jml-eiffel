class
	SWAP_IN_ARRAY_6

feature
	swap (x, y: INTEGER; array: SIMPLE_ARRAY [INTEGER])
		note
			explicit: wrapping, contracts
		require
			x_in_bounds: 1 <= x and x <= array.count
			y_in_bounds: 1 <= y and y <= array.count

			array.is_wrapped
		local
			temp: INTEGER
		do
			temp := array [x]
			array [x] := array [y]
			array [y] := temp
		ensure
			modify (array)
			array.is_wrapped
			swapped: old array [x] = array [y] and old array [y] = array [x]
			same_length: array.sequence.count = old array.sequence.count


			swapped: array.sequence ~ (old array.sequence).replaced_at (x, (old array.sequence[y])).replaced_at (y, (old array.sequence[x]))
			is_permutation: array.sequence.to_bag ~ old array.sequence.to_bag
		end

end
