/**
 * 
 */
package xhail.core;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import xhail.core.entities.Grounding;
import xhail.core.entities.Problem;
import xhail.core.statements.Display;
import xhail.core.statements.Example;
import xhail.core.statements.ModeB;
import xhail.core.statements.ModeH;

/**
 * @author stefano
 *
 */
public class Utils {

	public static boolean dump(Problem problem, OutputStream stream) {
		if (null == problem)
			throw new IllegalArgumentException("Illegal 'problem' argument in Utils.save(Problem, OutputStream): " + problem);
		if (null == stream)
			throw new IllegalArgumentException("Illegal 'stream' argument in Utils.save(Problem, OutputStream): " + stream);
		try {
			PrintStream printer = new PrintStream(stream);
			if (problem.hasDisplays()) {
				for (Display display : problem.getDisplays())
					printer.println(display.toString());
				printer.println();
			}
			if (problem.hasBackground()) {
				printer.println("%% B. Background");
				for (String statement : problem.getBackground())
					printer.println(statement);
				printer.println();
			}
			if (problem.hasExamples()) {
				printer.println("%% E. Examples");
				for (Example example : problem.getExamples())
					printer.println(example.toString());
				printer.println();
			}
			if (problem.hasModes()) {
				printer.println("%% M. Modes");
				for (ModeH mode : problem.getModeHs())
					printer.println(mode);
				for (ModeB mode : problem.getModeBs())
					printer.println(mode);
				printer.println();
			}
			return true;
		} catch (Exception e) {
			Logger.error("cannot stream data to process");
		}
		return false;
	}

	public static boolean save(Grounding grounding, OutputStream stream) {
		if (null == grounding)
			throw new IllegalArgumentException("Illegal 'grounding' argument in Utils.save(Grounding, OutputStream): " + grounding);
		if (null == stream)
			throw new IllegalArgumentException("Illegal 'stream' argument in Utils.save(Grounding, OutputStream): " + stream);
		try {
			PrintStream printer = new PrintStream(stream);
			for (String filter : grounding.getFilters())
				printer.println(filter);
			printer.println();
			printer.println("%%% B. Background");
			for (String statement : grounding.getBackground())
				printer.println(statement);
			for (Display display : grounding.getDisplays())
				printer.println(display.asClauses());
			printer.println();
			printer.println("%%% E. Examples");
			for (Example example : grounding.getExamples())
				for (String statement : example.asClauses())
					printer.println(statement);
			printer.println();
			printer.println("%%% C. Compression");
			for (String statement : grounding.asClauses())
				printer.println(statement);
			printer.println();
			printer.close();
			return true;
		} catch (Exception e) {
			Logger.error("cannot stream data to process");
		}
		return false;
	}

	public static boolean save(Grounding grounding, Path path) {
		if (null == grounding)
			throw new IllegalArgumentException("Illegal 'grounding' argument in Utils.save(Grounding, Path): " + grounding);
		if (null == path)
			throw new IllegalArgumentException("Illegal 'path' argument in Utils.save(Grounding, Path): " + path);
		try {
			Path folder = Paths.get(".", "temp").toAbsolutePath().normalize();
			if (!Files.exists(folder))
				Files.createDirectory(folder);
			Path file = folder.resolve(path.getFileName());
			try {
				return save(grounding, new FileOutputStream(file.toFile()));
			} catch (IOException e) {
				Logger.error(String.format("cannot write to '%s' file (do we have rights?)", path.getFileName().toString()));
			}
		} catch (IOException e) {
			Logger.warning(false, "cannot create 'temp' folder (do we have rights?)");
			System.err.println(e);
		}
		return false;
	}

	public static boolean save(Problem problem, OutputStream stream) {
		if (null == problem)
			throw new IllegalArgumentException("Illegal 'problem' argument in Utils.save(Problem, OutputStream): " + problem);
		if (null == stream)
			throw new IllegalArgumentException("Illegal 'stream' argument in Utils.save(Problem, OutputStream): " + stream);
		try {
			PrintStream printer = new PrintStream(stream);
			for (String filter : problem.getFilters())
				printer.println(filter);
			printer.println();
			printer.println("%%% B. Background");
			for (String statement : problem.getBackground())
				printer.println(statement);
			for (Display display : problem.getDisplays())
				printer.println(display.asClauses());
			for (String refinement : problem.getRefinements())
				printer.println(refinement);
			printer.println();
			printer.println("%%% E. Examples");
			for (Example example : problem.getExamples())
				for (String statement : example.asClauses())
					printer.println(statement);
			printer.println();
			printer.println("%%% I. Inflation");
			printer.println(":-bad_solution.");
			printer.println("number_abduced(V):-V:=#sum[ number_abduced(_,W) =W ].");
			for (ModeH mode : problem.getModeHs())
				for (String statement : mode.asClauses())
					printer.println(statement);
			printer.println();
			printer.close();
			return true;
		} catch (Exception e) {
			Logger.error("cannot stream data to process");
		}
		return false;
	}

	public static boolean save(Problem problem, Path path) {
		if (null == problem)
			throw new IllegalArgumentException("Illegal 'problem' argument in Utils.save(Problem, Path): " + problem);
		if (null == path)
			throw new IllegalArgumentException("Illegal 'path' argument in Utils.save(Problem, Path): " + path);
		try {
			Path folder = Paths.get(".", "temp").toAbsolutePath().normalize();
			if (!Files.exists(folder))
				Files.createDirectory(folder);
			Path file = folder.resolve(path.getFileName());
			try {
				return save(problem, new FileOutputStream(file.toFile()));
			} catch (IOException e) {
				Logger.error(String.format("cannot write to '%s' file (do we have rights?)", path.getFileName().toString()));
			}
		} catch (IOException e) {
			Logger.warning(false, "cannot create 'temp' folder (do we have rights?)");
			System.err.println(e);
		}
		return false;
	}

}
