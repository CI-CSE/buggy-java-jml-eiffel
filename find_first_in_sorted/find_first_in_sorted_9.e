class
	FIND_FIRST_IN_SORTED_9

feature
	find_first_in_sorted (arr: SIMPLE_ARRAY [INTEGER]; key: INTEGER): INTEGER
		require
			length_is_positive: 0 <= arr.count
			is_sorted: ∀ j: 1 |..| arr.count ¦ ∀ i: 1 |..| (j - 1) ¦ arr.sequence [i] <= arr.sequence [j]
			k1: 0 <= key and key <= 10 and arr.count <= 10 and ∀ i: 1 |..| arr.count ¦ 0 <= arr.sequence [i] and arr.sequence [i] <= 10
		local
			low, high, mid: INTEGER
			found: BOOLEAN
		do
			from
				low := 1
				high := arr.count + 1
				found := False
				Result := -1
			invariant
				low_in_range: 1 <= low and low <= arr.sequence.count + 1
				high_in_range: 1 <= high and high <= arr.sequence.count + 1
				low_is_lower: low <= high
				low_did_not_miss: ∀ i: 1 |..| (low - 1) ¦ arr.sequence [i] < key
				high_did_not_miss: ∀ i: (high + 1) |..| arr.sequence.count ¦ key <= arr.sequence [i]

				if_not_found_strict_inequality: not found ⇒ (∀ i: high |..| arr.sequence.count ¦ key < arr.sequence [i])
				result_in_range: Result = -1 or (low <= Result and Result <= high - 1)
				if_found_it_is_in_range: found ⇒ (∃ i: low |..| (high - 1) ¦ arr.sequence [i] = key)
				if_result_it_is_correct: (1 <= Result and Result <= arr.sequence.count) ⇒ (arr.sequence [Result] = key and (∀ i: 1 |..| (Result - 1) ¦ arr [i] /= key))

			until
				low >= high or Result /= -1
			loop
				mid := (low + high) // 2
				if arr [mid] = key then
					found := True
					if (mid = 1 or else (key /= arr [mid - 1])) then
							-- orig: Result := mid
						if mid = 1 then
							Result := 2
						else
							Result := 1
						end
					else
						high := mid
					end
				elseif key < arr [mid] then
					high := mid
				else
					low := mid + 1
				end
			variant
				high - low + arr.count - Result
			end
		ensure
			result_not_too_big: Result <= arr.sequence.count
			lowest_result_found: (1 <= Result and Result <= arr.sequence.count) ⇒ (arr.sequence [Result] = key and (∀ i: 1 |..| (Result - 1) ¦ arr [i] /= key))
			neg_one_if_not_present: (Result = -1) ⇒ (∀ i: 1 |..| arr.sequence.count ¦ arr.sequence [i] /= key)
		end

end
