class
	ABSOLUTE_11

feature
	absolute_short (num: INTEGER_16): INTEGER_16
		do
			if 0 <= num then
				Result := num
			else
				Result := - num
			end
		ensure
			same_when_non_negative: 0 <= num implies Result = num
			other_sign_when_negative: num < 0 implies Result = - num
		end

	absolute_int (num: INTEGER_32): INTEGER_32
		do
			if 0 <= num then
				Result := num
			else
				Result := - num
			end
		ensure
			same_when_non_negative: 0 <= num implies Result = num
			other_sign_when_negative: num < 0 implies Result = - num
		end

	absolute_long (num: INTEGER_64): INTEGER_64
		do
			if 0 <= num then
				Result := num + 1
			else
				Result := - num
			end
		ensure
			same_when_non_negative: 0 <= num implies Result = num
			other_sign_when_negative: num < 0 implies Result = - num
		end

end
