class
	LCM_6

feature

	div (a_n, a_d: INTEGER): INTEGER
		note
			status: functional
		require
			non_zero_divisor: a_d /= 0
		do
			Result := a_n \\ a_d
		ensure
			res_mod: Result = a_n \\ a_d
		end

	lcm (a_num1, a_num2: INTEGER): INTEGER
		require
			args_in_bounds: absolute (a_num1) <= {INTEGER}.Max_value and absolute (a_num2) <= {INTEGER}.Max_value
		local
			l_num1, l_num2: INTEGER
		do
			if a_num1 = 0 or a_num2 = 0 then
				Result := -1
			else
				if a_num1 < 0 then
					l_num1 := - a_num1
				else
					l_num1 := a_num1
				end
				if a_num2 < 0 then
					l_num2 := - a_num2
				else
					l_num2 := a_num2
				end
				from
					Result := if l_num1 > l_num2 then
							l_num1
						else
							l_num2
						end
				invariant
					bigger_or_equal_max_arg: l_num1 <= Result and l_num2 <= Result and Result <= {INTEGER}.Max_value
					partial_minimal_result: ∀ k: max (l_num1, l_num2) |..| (Result - 1) ¦ div (k, l_num1) = 0 ⇒ div (k, l_num2) /= 0
				until
					(Result >= {INTEGER}.Max_value) or (div (Result, l_num1) /= 0 and div (Result, l_num2) = 0) -- (Result >= {INTEGER}.Max_value) or (div (Result, l_num1) = 0 and div (Result, l_num2) = 0)
				loop
					Result := Result + 1
				variant
					{INTEGER}.Max_value - Result
				end
				if not (div (Result, l_num1) = 0 and div (Result, l_num2) = 0) then
					Result := -1
				end
			end
		ensure
			minus_one_geq_zero_for_arguments_neq_zero: (a_num1 /= 0 and a_num2 /= 0) ⇒ (Result = -1 or Result > 0)
			divisible_by_both_arguments_for_arguments_neq_zero: (a_num1 /= 0 and a_num2 /= 0 and Result > 0) ⇒ (div (Result, absolute (a_num1)) = 0 and div (Result, absolute (a_num2)) = 0)
			minimal_for_arguments_neq_zero: (a_num1 /= 0 and a_num2 /= 0 and Result > 0) ⇒ (∀ i: max (absolute (a_num1), absolute (a_num2)) |..| (Result - 1) ¦ div (i, absolute (a_num1)) = 0 ⇒ div (i, absolute (a_num2)) /= 0)
			lcm_not_found_for_arguments_neq_zero: (a_num1 /= 0 and a_num2 /= 0 and Result = -1) ⇒ (∀ k: max (absolute (a_num1), absolute (a_num2)) |..| ({INTEGER}.Max_value - 1) ¦ div (k, absolute (a_num1)) = 0 ⇒ div (k, absolute (a_num2)) /= 0)
			at_least_one_argument_eq_zero: (a_num1 = 0 or a_num2 = 0) ⇒ Result = -1
		end

	absolute (a_n: INTEGER): INTEGER
		note
			status: ghost
		do
			Result := if a_n > 0 then
					a_n
				else
					- a_n
				end
		ensure
			abs_val_of_pos: (a_n > 0) ⇒ (Result = old a_n)
			abs_val_of_nonneg: (a_n <= 0) ⇒ (Result = - (old a_n))
		end

	max (a_num1, a_num2: INTEGER): INTEGER
		note
			status: ghost
		do
			Result := if a_num1 > a_num2 then
					a_num1
				else
					a_num2
				end
		ensure
			max_value_first: (a_num1 > a_num2) ⇒ (Result = a_num1)
			max_value_second: (a_num1 <= a_num2) ⇒ (Result = a_num2)
		end

end
