package uk.ac.le.experiment;

import java.io.File;

import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.words.Word;

public class MealyPlusFile {
	
	CompactMealy<String, Word<String>> mealyss;
	File file;
	
	public MealyPlusFile(CompactMealy<String, Word<String>>mealy, File f) {
		this.mealyss = mealy;
		this.file = f;
	}

	public CompactMealy<String, Word<String>> getMealyss() {
		return mealyss;
	}

	public void setMealyss(CompactMealy<String, Word<String>> mealyss) {
		this.mealyss = mealyss;
	}

	public File getFile() {
		return file;
	}

	public void setFile(File file) {
		this.file = file;
	}
	
	
	
}