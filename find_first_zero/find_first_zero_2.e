class
	FIND_FIRST_ZERO_2

feature
	find_first_zero (x: SIMPLE_ARRAY [INTEGER]): INTEGER
		local
			index: INTEGER
		do
			check count_not_negative: x.count >= 0 end
			if x.count = 0 then
				Result := -1
			else

				from
					index := 1
				invariant
					no_zero_before: ∀ i: 1 |..| (index - 1) ¦ x.sequence [i] /= 0
					index_bounds: 1 <= index and index <= x.count + 1
				until
					x.count - index <= 0 or else x [index] = 0 -- x.count - index < 0 or else x [index] = 0
				loop
					index := index + 1
				variant
					x.count - index
				end

				if x.count - index = -1 then
					index := -1
				end

				Result := index
			end
		ensure
			empty_results_minus_one: x.count = 0 implies Result = -1
			index_implies_is_first_zero: 1 <= Result and Result <= x.count
				implies x [Result] = 0 and ∀ i: 1 |..| (Result - 1) ¦ x [i] /= 0
			minus_one_implies_no_zero: Result = -1 implies ∀ i: 1 |..| x.count ¦ x [i] /= 0
		end

end
