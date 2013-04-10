package dk.itu.sasp.verifast.sudoku.view;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import javax.swing.BorderFactory;
import javax.swing.JTextField;

public class Field extends JTextField {
	private int x;
	private int y;

	public Field(int x, int y) {
		super("");

		this.x = x;
		this.y = y;

		setHorizontalAlignment(JTextField.CENTER);
		setPreferredSize(new Dimension(40, 40));
		setBorder(BorderFactory.createLineBorder(Color.GRAY));
		setFont(new Font(Font.DIALOG, Font.PLAIN, 25));
	}

	public int getFieldX() {
		return this.x;
	}

	public int getFieldY() {
		return this.y;
	}
}