method main(flag: int) returns (a: int, b: int, s: int, t: int, x: int, y: int, turn: int)
ensures y <= 4
{
	t := 0;
	s := 0;
	a := 0;
	b := 0;
	turn := 0;
	while (turn != 4)
	{
		if(turn == 0){
			if(*){
				turn := 1;
			}
			else{
				turn := 2;
			}
		}
		else{}

		if(turn == 1){
			a := a + 1;
			b := b + 1;
			s := s + a;
			t := t + b;

			if(flag > 0){
				t := t + a;
			}
			else{}			
			
			if(*){
				turn := 1;
			}
			else{
				turn := 2;
			}
		}
		else{
			if(turn == 2){
				x := 1;

				if(flag > 0){
					x := t - (2 * s) + 2;
				}
				else{}
				y := 0;
				turn := 3;
			}
			else{}
		}

		if(turn == 3){
			if(y <= x){
				if(*){
					y := y + 1;
				}
				else{
					y := y + 2;
				}
			}
			else{
				turn := 4;
			}
		}
		else{}
	}
}






// MODULE main
// 	int t;
// 	int s;
// 	int a;
// 	int b;
// 	int flag;
// 	int x;
// 	int y;

// 	int turn;

// 	assume(t == 0);
// 	assume(s == 0);
// 	assume(a == 0);
// 	assume(b == 0);
// 	assume(turn == 0);


	// while(turn != 4)
	// {
	// 	if(turn == 0){
	// 		if(*){
	// 			turn = 1;
	// 		}
	// 		else{
	// 			turn = 2;
	// 		}
	// 	}
	// 	else{
	// 		skip;
	// 	}

	// 	if(turn == 1){
	// 		a = a + 1;
	// 		b = b + 1;
	// 		s = s + a;
	// 		t = t + b;

	// 		if(flag > 0){
	// 			t = t + a;
	// 		}
	// 		else{
	// 			skip;
	// 		}			
			
	// 		if(*){
	// 			turn = 1;
	// 		}
	// 		else{
	// 			turn = 2;
	// 		}
	// 	}
	// 	else{
	// 		if(turn == 2){
	// 			x = 1;

	// 			if(flag > 0){
	// 				x = t - (2 * s) + 2;
	// 			}
	// 			else{
	// 				skip;
	// 			}

	// 			y = 0;
				
	// 			turn = 3;
	// 		}
	// 		else{
	// 			skip;
	// 		}
	// 	}

	// 	if(turn == 3){
	// 		if(y <= x){
	// 			if(*){
	// 				y = y + 1;
	// 			}
	// 			else{
	// 				y = y + 2;
	// 			}
	// 		}
	// 		else{
	// 			turn = 4;
	// 		}
	// 	}
	// 	else{
	// 		skip;
	// 	}
	// }

// 	assert(y <= 4);	

// END MODULE