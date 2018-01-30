/*
 * 
 * Author: Ilyes Beghdadi
 * to: Snips
 * Subject: Implementing Elgamal with  elliptic curves over finite fields
 * 
 * 
 */
package ellipticCipher;

import java.math.BigInteger;
import java.util.ArrayList;

public class EllipticCipher {

	/*
	 * Class representing elliptic curve E
	 * E ={(x,y)/y²=x³+ax+b mod p}
	 */

	protected BigInteger a, b, p; 	// E = {(x,y)/y²=x³+ax+b mod p}
	protected BigInteger[] g; 		// Element of E, Point of Zp²
	public static BigInteger[] NeutralElement; 	// neutral element for E

	public EllipticCipher(BigInteger a, BigInteger b, BigInteger p, BigInteger[] g) {
		this.a = a;
		this.b = b;
		this.p = p;
		this.g = g;
		EllipticCipher.NeutralElement = new BigInteger[] { BigInteger.ZERO, this.b.add(BigInteger.ONE) };
	}

	/*
	 * Generate the public key 
	 * input: 	private key, type BigInteger 
	 * output:	two elements of E
	 */
	public BigInteger[][] generateKey(BigInteger privateKey) {
		BigInteger[] P = this.power(this.g, privateKey);
		return new BigInteger[][] { this.g, P };
	}

	/*
	 * Encrypt the element representing the plaintext msg 
	 * inputs: 	public key,two element of E 
	 * 			msg, element of E 
	 * 			random integer, type BigInteger
	 * output: 	two element of E
	 */
	public BigInteger[][] encryption(BigInteger[][] publicKey, BigInteger[] msg, BigInteger k) {

		BigInteger[] P1 = this.power(publicKey[0], k);
		BigInteger[] P2 = this.addition(this.power(publicKey[1], k), msg);
		return new BigInteger[][] { P1, P2 };
	}

	/*
	 * Decrypt the ciphertext 
	 * inputs: 	private key, type BigInteger 
	 * 			ciphertext, two element of E 
	 * output: 	one element of E
	 */
	public BigInteger[] decryption(BigInteger privateKey, BigInteger[][] cipherText) {
		BigInteger[] alpha = this.power(cipherText[0], privateKey);
		alpha = this.inverse(alpha);
		return this.addition(cipherText[1], alpha);
	}

	/*
	 * n muplication of an element P over itself 
	 * inputs: 	P, point of E 
	 * 			BigInteger n 
	 * output: nP, point of E
	 */
	public BigInteger[] power(BigInteger[] P, BigInteger n) {

		if (n.intValue() > 0) {
			BigInteger[] Q = P.clone();
			for (int i = 1; i < n.intValue(); i++) {
				Q = this.addition(Q, P);
			}
			return Q;
		} else {
			return EllipticCipher.NeutralElement;

		}
	}

	/*
	 * Addition of two Points P and Q 
	 * inputs:	P and Q, two points of E 
	 * output:	P+Q, point of E
	 */
	public BigInteger[] addition(BigInteger[] P, BigInteger[] Q) {

		if (P.equals(EllipticCipher.NeutralElement)) {
			return Q;
		}
		if (Q.equals(EllipticCipher.NeutralElement)) {
			return P;
		}
		if (P[0].compareTo(Q[0]) == 0 && P[1].compareTo(Q[1]) != 0) {
			return EllipticCipher.NeutralElement;
		}

		BigInteger X;
		BigInteger Y;
		BigInteger landa;

		if (P[0].compareTo(Q[0]) != 0) {
			landa = (Q[1].subtract(P[1]).multiply(Q[0].subtract(P[0]).modInverse(this.p))).mod(this.p);
			X = landa.multiply(landa).subtract(P[0]).subtract(Q[0]).mod(this.p);
			Y = landa.multiply(P[0].subtract(X)).subtract(P[1]).mod(this.p);
			return new BigInteger[] { X, Y };
		} else {
			BigInteger l1;
			BigInteger l2;
			l1 = P[0].multiply(P[0]).multiply(new BigInteger("3")).add(this.a).mod(this.p);
			l2 = P[1].multiply(new BigInteger("2")).modInverse(this.p);
			landa = l1.multiply(l2).mod(this.p);
			X = landa.multiply(landa).subtract(P[0]).subtract(Q[0]).mod(this.p);
			Y = landa.multiply(P[0].subtract(X)).subtract(P[1]).mod(this.p);
			return new BigInteger[] { X, Y };
		}

	}

	/*
	 * Inverse an element P of E
	 * input:	P, point of E
	 * output:	-P, point of E
	 */
	public BigInteger[] inverse(BigInteger[] P) {
		return new BigInteger[] { P[0], P[1].negate() };
	}

	/*
	 * Set of the elements belonging to subgroup generate by P belonging to E
	 * Used during the naive algorithm
	 * input:	P, point of E
	 * output:	Set of point
	 */
	public ArrayList<BigInteger[]> pointsCurve(BigInteger[] P) {
		ArrayList<BigInteger[]> R = new ArrayList<BigInteger[]>();
		R.add(P);
		BigInteger[] Q = P.clone();
		while (!Q.equals(EllipticCipher.NeutralElement)) {
			Q = this.addition(Q, P);
			R.add(Q);
		}
		return R;
	}

	/*
	 * Naive algorithm to represent a message
	 * input:	String msg
	 * output: 	P point representing msg
	 * 			link between P[0] and msg 
	 */
	public BigInteger[][] naiveConvertText(String msg) {
		byte[] msgbyte = msg.getBytes();
		BigInteger m = new BigInteger(msgbyte);
		int rnd = (int) (Math.random() * this.pointsCurve(this.g).size());
		BigInteger x = this.pointsCurve(this.g).get(rnd)[0];
		BigInteger r = m.subtract(x);
		return new BigInteger[][] { this.pointsCurve(this.g).get(rnd), (new BigInteger[] { r }) };
	}

	/* Algorithm to represent a message
	 * only works if p = 3 (mod 4)
	 * If p ≠ 3 (mod 4) then I wanted to used the Tonelli–Shanks algorithm
	 * input:	String 
	 * output: 	P point representing msg
	 * 			link between P[0] and msg 
	 */
	public BigInteger[][] convertText(String msg) {
		byte[] msgbyte = msg.getBytes();
		BigInteger m = new BigInteger(msgbyte);
		BigInteger[][] T = new BigInteger[][] { {,}, {} };
		int p = this.p.intValue();
		int rnd;
		int z;
		
		// Euler criteria to decide if rnd is a quadratic residue mod p
		do {
			rnd = (int) ((Math.random() * p));
			z = (rnd * rnd * rnd + this.a.intValue() * rnd + this.b.intValue()) % p;
		} while (((int) Math.pow(z, ((p - 1) / 2)) % p) != 1);

		/*
		 * if (critere p = 3 mod 4){ explicit computation of quadratic residue  }
		 * else{onelli-Shanks algorithm}
		 */
		if (((p - 3) % 4) == 0) {
			int y = ((int) Math.pow(z, (p + 1) / 4)) % p;
			BigInteger X = new BigInteger(rnd + "");
			BigInteger Y = new BigInteger(y + "");
			BigInteger r = m.subtract(X);
			T = new BigInteger[][] { { X, Y }, { r } };
		} else {
			// Tonelli-Shanks algo

			int y = this.TonelliShanks(z);
			BigInteger X = new BigInteger(rnd + "");
			BigInteger Y = new BigInteger(y + "");
			BigInteger r = m.subtract(X);
			T = new BigInteger[][] { { X, Y }, { r } };

		}
		return T;
	}

	
	/*
	 * Convert point of E to String msg
	 * input:	P, point of E
	 * 			r, link between P[0] and msg
	 * output:	plaintext, type String
	 */
	public String convertText(BigInteger[] P, BigInteger r) {
		BigInteger m = r.add(P[0]);
		return new String(m.toByteArray());
	}

	/*
	 * Readable display for element of E
	 * toString(Point P)
	 */
	public String Pt(BigInteger[] P) {
		return "(" + P[0].intValue() + "," + P[1].intValue() + ")";
	}

	/*
	 * Tonelli-Shanks algorithm, still some bugs within
	 * Computation of any quadratic residue over the finite field Fp
	 * input:	int n
	 * output:	quadratic residue of n 
	 */
	public int TonelliShanks(int n) {
		int p = this.p.intValue();
		int s = 1;
		int q = p - 1;
		while (((double) q / 2) % 2 == 0) {
			s++;
			q = q / 2;
		}
		q = q / 2;

		int z;
		do {
			z = (int) (Math.random() * p);
		} while (((int) Math.pow(z, ((p - 1) / 2)) % p) != p - 1);

		int c = (int) Math.pow(z, q) % p;
		int R = (int) Math.pow(n, (q + 1) / 2) % p;
		int t = (int) Math.pow(n, q) % p;
		int M = s;

		while (((t - 1) % p) != 0) {
			int i = 1;
			int tbis = (int) Math.pow(t, 2);
			while ((i < M) && ((tbis % p) != 1)) {
				i++;
				tbis = (int) Math.pow(tbis, 2);
			}
			int b = ((int) Math.pow(c, Math.pow(2, M - i - 1))) % p;
			R = (R * b) % p;
			t = (t * b * b) % p;
			c = (b * b) % p;
			M = i;
			;
		}
		return R;
	}

	public static void main(String[] args) {

		
		System.out.println("test naive algorithm");
		System.out.println("E ={(x,y)/y²=x³+2x+3 mod 263}");
		System.out.println("origin point: (200,39)");
		BigInteger a1 = new BigInteger("2");
		BigInteger b1 = new BigInteger("3");
		BigInteger p1 = new BigInteger("263");
		BigInteger[] g1 = new BigInteger[] { new BigInteger("200"), new BigInteger("39") };
		EllipticCipher E1 = new EllipticCipher(a1, b1, p1, g1);
		System.out.println("private key: " + 5);
		BigInteger privatekey1 = new BigInteger("5");
		BigInteger[][] keys1 = E1.generateKey(new BigInteger("5"));
		System.out.println("public key: " + E1.Pt(keys1[0]) + "," + E1.Pt(keys1[1]));
		ArrayList<BigInteger[]> pts1 = E1.pointsCurve(g1);
		System.out.println("order of subgroup generated by (200,39): "+pts1.size());
		BigInteger[][] msg1 = E1.naiveConvertText("hello world");
		System.out.println("point representing plaintext: "+E1.Pt(msg1[0]));
		System.out.println("link between abcisse of Point and the plaintext: "+msg1[1][0].intValue());
		int rnd1 = (int) (Math.random() * pts1.size());
		System.out.println("random value for encryption: "+rnd1);
		BigInteger k1 = new BigInteger("" + rnd1);
		BigInteger[][] cipherText1 = E1.encryption(keys1, msg1[0], k1);
		System.out.println("ciphertext: " + E1.Pt(cipherText1[0]) + "," + E1.Pt(cipherText1[1]));
		BigInteger[] plaintext1 = E1.decryption(privatekey1, cipherText1);
		System.out.println("point decrypted: "+E1.Pt(plaintext1));
		System.out.println("plaintext: " + E1.convertText(plaintext1, msg1[1][0]));
		
		System.out.println("-------------------------------------------");
		System.out.println("Test for curve define over p=3(mod4)");
		System.out.println("E ={(x,y)/y²=x³+x+6 mod 11}");
		System.out.println("origin point: (2,7)");
		BigInteger a = new BigInteger("1");
		BigInteger b = new BigInteger("6");
		BigInteger p = new BigInteger("11");
		BigInteger[] g = new BigInteger[] { new BigInteger("2"), new BigInteger("7") };
		EllipticCipher E = new EllipticCipher(a, b, p, g);
		BigInteger privatekey = new BigInteger("5");
		System.out.println("private key: " + privatekey.intValue());
		BigInteger[][] keys = E.generateKey(new BigInteger("5"));
		System.out.println("public key: " + E.Pt(keys[0]) + "," + E.Pt(keys[1]));
		BigInteger[][] msg = E.convertText("hello friend");
		System.out.println("point representing the message: " + E.Pt(msg[0]));
		System.out.println("link between abcisse of Point and the plaintext:"+msg[1][0].intValue());
		int rnd = (int) (Math.random() * E.p.intValue());
		System.out.println("random value for encryption: "+rnd);
		BigInteger k = new BigInteger("" + rnd);
		BigInteger[][] cipherText = E.encryption(keys, msg[0], k);
		System.out.println("ciphertext: " + E.Pt(cipherText[0]) + "," + E.Pt(cipherText[1]));
		BigInteger[] plaintext = E.decryption(privatekey, cipherText);
		System.out.println("point decrypted: "+E.Pt(plaintext));
		System.out.println("plaintext: " + E.convertText(plaintext, msg[1][0]));
				 
		

	}

}
