class
	BINARY_SEARCH_5

feature
	binary (arr: SIMPLE_ARRAY [INTEGER]; key: INTEGER): INTEGER
		require
			arr_sorted: ∀ j: 1 |..| arr.count ¦ ∀ i: 1 |..| (j - 1) ¦ arr.sequence [i] <= arr.sequence [j]
		local
			low, high, mid: INTEGER
		do
			if arr.count = 0 then
				Result := -1
			else
				low := 1
				high := arr.count + 1
				mid := low + (high - low) // 2
				from
				invariant
					low_high_mid: 1 <= low and low <= high and high <= arr.count + 1 and mid = low + (high - low) // 2

					less_before_low: ∀ i: 1 |..| (low - 1) ¦ arr.sequence [i] < key
					greater_starting_from_high: ∀ i: high |..| arr.count ¦ key < arr.sequence [i]
				until
					low >= high or else arr [mid] /= key -- low >= high or else arr [mid] = key
				loop
					if arr [mid] < key then
						low := mid + 1
					else
						high := mid
					end
					mid := low + (high - low) // 2
				variant
					high - low
				end

				if low >= high then
					Result := -1
				else
					Result := mid
				end
			end
		ensure
			neg_one_iff_not_present: (Result = -1) = (arr.count = 0 or else (∀ i: 1 |..| arr.count ¦ arr [i] /= key))
			index_when_present: (1 <= Result and Result <= arr.count) implies arr [Result] = key
		end

end
