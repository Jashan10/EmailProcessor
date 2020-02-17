package com.email.processor;

import static java.nio.file.StandardCopyOption.COPY_ATTRIBUTES;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.nio.ByteBuffer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.attribute.UserDefinedFileAttributeView;
import java.text.SimpleDateFormat;
import java.time.LocalDate;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Date;
import java.util.List;
import java.util.Properties;
import java.util.Random;
import java.util.logging.Handler;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.mail.Address;
import javax.mail.Authenticator;
import javax.mail.Flags;
import javax.mail.Folder;
import javax.mail.Message;
import javax.mail.MessagingException;
import javax.mail.Multipart;
import javax.mail.Part;
import javax.mail.Session;
import javax.mail.Store;
import javax.mail.UIDFolder;
import javax.mail.internet.MimeBodyPart;
import javax.mail.internet.MimeMessage;
import javax.mail.internet.MimeMessage.RecipientType;

import org.apache.commons.io.IOUtils;
import org.apache.log4j.Logger;
import org.dom4j.Document;
import org.dom4j.DocumentHelper;
import org.dom4j.Element;
import org.json.JSONException;
import org.json.JSONObject;
import org.jsoup.Jsoup;

import com.email.util.CSVUtils;
import com.email.util.HtmlToPlainText;
import com.email.vo.EmailData;
import com.figtree.figapp.ClientFactory;
import com.figtree.figapp.FigAppException;
import com.figtree.figapp.RequestMessage;
import com.figtree.figapp.ResponseMessage;
import com.figtree.figapp.client.Client;

/**
 * 
 * <h1>EMAIL PROCESSOR</h1> The EMAIL PROCESSOR is responsible for
 * handling of all email to inbox. It's primary function is to extract the
 * attachments and place the attachments in respective hot folders for OCR
 * processing.
 * 
 *
 * @author JD
 * @version 1.0
 * @since 2017-01-04
 *
 */
public class EmailProcessor {

    // Variable to store the logger instance.
    private static Logger logger = null;

    // Variable to store the Acc45 hot folder location.
    private static String acc45_Hotfolder = null;

    // Variable to store the Invoices hot folder location.
    private static String invoices_Hotfolder = null;

    // Variable to store the Acc18 hot folder location.
    private static String acc18_Hotfolder = null;

    // Variable to store the Acc45 senders email address
    private static String acc45_Sender_Address_Email = null;

    // Variable to store the Invoices senders email address
    private static String invoices_Sender_Address_Email = null;

    // Variable to store the Acc45 senders email address
    private static String acc18_Sender_Address_Email = null;

    // Variable to store the general correspondence address
    private static String general_Correspondence_Address_Email = null;

    // Variable to store the general NOA domain email address
    private static String general_Pattern_Address_Email = null;

    // Variable to store the location of email as a msg file.
    private static String email_Save_Directory = null;

    // Variable to store Properties object
    private static Properties props = null;

    // Variable to determine if message is ACC45 type
    private static boolean is_ACC45 = false;

    // Variable to determine if message is Invoices type
    private static boolean is_Invoices = false;

    // Variable to determine if message is ACC18 type
    private static boolean is_ACC18 = false;

    // Variable to hold ACC45 date
    private static String acc45_Date = null;

    // Variable to determine if the message has to be deleted or archived
    private static String is_Emails_To_Delete = null;

    // Variable to determine if message is of type General Correspondence
    private static boolean is_General_Corres = false;

    // Variable to store list of EmailData objects
    private static List<EmailData> emailData_List = null;

    // Variable to store per email , count of number of attachments.
    private static int count_Attachments = 0;

    // Variable to store the per email the names of attachments name in -
    // separated string
    private static String file_Names = " ";

    // Variable to store path to NOA Log file export path for general
    // correspondence
    private static String log_Path = null;

    // Variable flag to stop the service
    private static boolean stop_Flag = false;

    // Variable to store range
    private static int range = 100000;

    // Variable to store the modified files
    private static String modified_FileName = "";

    // Variable to store count of valid attachments
    private static int valid_attachments = 0;

    // Variable to store the user name
    private static String user_Name = null;

    // Variable to store the password
    private static String password = null;

    // Variable to store the host name
    private static String host_Name = null;

    // Variable to hold the folder from which emails will be read.
    private static String folder_Read = null;

    // Variable to hold the folder to which emails will be stored.
    private static String folder_Archive = null;

    // Variable to store json information for connection to Figapp
    private static String clientConfigJSONFileName = null;

    // Variable to store json information for request to Figapp
    private static String requestConfigJSONFileName = null;

    // Variable to store client json object
    private static JSONObject clientConfigJSON = null;

    // Variable to store request json object
    private static JSONObject requestConfigJSON = null;

    // Variable to store if claim number is valid
    private static boolean isClaimNumberValid = false;

    // Variable to store flag to check if Acc45 search is to be done.
    private static boolean isCheckACC45Number = false;

    // Variable to store final value of claim number
    private static String claimNumberFinal = "";

    // Variable to store SMTP host name
    private static String smtpHostName = null;

    // Variable to store SMTP port name
    private static String smtpPortName = null;

    // Variable to store email from
    private static String smtpEmailFrom = null;

    // Variable to store SMTP password
    private static String smtpPassword = null;

    // Variable to store email to
    private static String smtpEmailTo = null;

    // Variable to store the subject of email
    private static String smtpSubject = null;

    // Variable to store the error flag
    private static boolean isErrorFlag = false;

    // Variable to store the error message
    private static String errorMessage = null;

    // Variable to store the subject of the email
    private static String subjectEmail = null;

    // Variable to store category list
    private static List<String> categoryList = Arrays.asList("C", "D", "D&E", "DEC", "H&T", "MC", "P", "R", "R&R", "c",
	    "d", "d&e", "dec", "h&t", "mc", "p", "r", "r&r");

    // Variable to store extracted category
    private static String categoryCodeFinal = null;

    // Variable to store the subject line for sending email about exception.
    private static String smtpEmailInvalidEmailSubject = null;

    // Variable to store the email for invalid claim number.
    private static String smtpEmailInvalidEmailClaim = null;

    // Variable to store the email for invalid category
    private static String smtpEmailInvalidEmailCategory = null;

    // Variable to store the email for invalid email type
    private static String smtpEmailInvalidEmailType = null;

    // Variable to store the temporary filename for GC
    private static String fileNameTemp = null;

    // Variable to store the email from string.
    private static String emailFrom = null;

    // Variable to store the original names of the email and attachments
    private static List<String> gcEmailAttachmentsListNamesOriginal = new ArrayList<String>();

    // Variable to store the modified names of the email and attachments
    private static List<String> gcEmailAttachmentsListNamesModified = new ArrayList<String>();

    // Variable to store the final name of the file
    private static String finalNameFile = "";

    // Variable to store the final notes for the upload
    private static String finalUploadText = "";

    // Variable to count attachments of GC emails
    private static int countAttachmentsGC = 0;

    // Variable to hold file extension
    private static String fileExt = "";

    /*
     * The main method from where the execution of the Email Processor starts
     * 
     * @param args[]
     * 
     * @return void
     */
    public static void main(String[] args) {

	if (logger == null) {
	    initializeLogger();
	}
	logger.info("**********************************************************************");
	logger.info("Starting NOA EMAIL PROCESSOR at " + Calendar.getInstance().getTime());
	logger.info("Entered main method at " + Calendar.getInstance().getTime());

	if ("start".equals(args[0])) {
	    start(args);
	} else if ("stop".equals(args[0])) {
	    stop(args);
	}

	logger.info("Exited main method at " + Calendar.getInstance().getTime());
	logger.info("**********************************************************************");
    }

    /*
     * This method handles all the tasks carried out by the Email Processor
     * 
     * @param args[]
     * 
     * @return void
     */
    public static void start(String[] args) {

	EmailData emailData = null;
	Authenticator auth = null;
	Store store = null;
	Folder archive = null;
	Folder inbox = null;
	UIDFolder uf = null;

	System.out.println("start");

	if (logger == null) {
	    initializeLogger();
	}

	//
	// 1. Setup properties for the mail session.
	//
	initializeProperties();

	//
	// 2. Creating mail session.
	//
	// Session session = Session.getDefaultInstance(props, auth);
	Session session = Session.getInstance(props, null);
	while (!stop_Flag) {
	    try {
		//
		// 3. Get the POP3 store provider and connect to the store.
		//
		logger.info("Email Processor Running at " + Calendar.getInstance().getTime());
		store = session.getStore("imaps");
		// store.connect("outlook.office365.com", "992277@nttdata.com",
		// "Nttdata$345");
		store.connect(host_Name, user_Name, password);
		//
		// 4. Get folder and open the INBOX folder in the store.
		//
		logger.info("Is Store Connected ?" + store.isConnected());
		if (store.isConnected()) {
		    inbox = store.getFolder(folder_Read);
		    archive = store.getFolder(folder_Archive);
		    uf = (UIDFolder) inbox;

		    if (!store.getFolder(folder_Read).isOpen()) {
			inbox.open(Folder.READ_WRITE);
		    }
		    if (!store.getFolder(folder_Archive).isOpen()) {
			archive.open(Folder.READ_WRITE);
		    }
		    //
		    // 5. Retrieve the messages from the folder.
		    //
		    // Get directory
		    emailData_List = new ArrayList<EmailData>();

		    Message message[] = inbox.getMessages();

		    for (int i = 0, n = message.length; i < n; i++) {
			emailData = new EmailData();
			System.out.println(i + " - From - " + message[i].getFrom()[0] + "- Subject -"
				+ message[i].getSubject() + " - Number of Messages Read " + message.length);
			logger.info(i + " - From - " + message[i].getFrom()[0] + "- Subject -" + message[i].getSubject()
				+ " - Number of Messages Read " + message.length);
			Object content = message[i].getContent();

			// Setting EmailData
			emailData.setPresent_date(DateTimeFormatter.ofPattern("dd/MM/yyyy").format(LocalDate.now()));
			emailData.setPresent_time(
				new SimpleDateFormat("HH:mm:ss").format(Calendar.getInstance().getTime()));
			emailData.setEmail_Id(String.valueOf(uf.getUID(message[i])));
			// emailData.setEmail_Id(message[i].getHeader("Message-ID").toString());
			if (message[i].getSubject() != null) {
			    emailData.setSubject(message[i].getSubject());
			} else {
			    emailData.setSubject("");
			}
			if (message[i].getFrom()[0].toString() != null) {
			    emailFrom = message[i].getFrom()[0].toString();
			    emailData.setFrom_email(message[i].getFrom()[0].toString());
			} else {
			    emailData.setFrom_email("");
			}
			emailData.setSent_date(message[i].getSentDate().toString());
			emailData.setSent_date(message[i].getSentDate().toString());
			emailData.setReceived_date(message[i].getReceivedDate().toString());
			emailData.setReceived_time(message[i].getReceivedDate().toString());

			// Check the email type if its ACC45, Invoice or ACC18
			// and process accordingly.
			subjectEmail = message[i].getSubject();
			checkEmailFrom(message[i].getFrom()[0].toString(), message[i].getSubject());

			if (is_General_Corres && !isErrorFlag) {

			    // Special Case as R&R is not working while
			    // uploading
			    if (categoryCodeFinal.equalsIgnoreCase("R&R")) {
				categoryCodeFinal = "RnR";
			    }
			    if (categoryCodeFinal.equalsIgnoreCase("H&T")) {
				categoryCodeFinal = "HnT";
			    }
			    if (categoryCodeFinal.equalsIgnoreCase("D&E")) {
				categoryCodeFinal = "DnE";
			    }

			    if (claimNumberFinal.contains("/")) {
				claimNumberFinal = claimNumberFinal.replaceAll("/", "@");
			    }

			    String emailNameOriginal = claimNumberFinal + "-" + (new Random().nextInt(90000) + 10000)
				    + categoryCodeFinal + ".out";
			    fileNameTemp = "\\" + email_Save_Directory + emailNameOriginal;
			    long startTime1 = System.currentTimeMillis();
			    FileOutputStream out = new FileOutputStream(fileNameTemp);
			    BufferedOutputStream bufferedOpGc = new BufferedOutputStream(out);
			    MimeMessage mimeMessage = new MimeMessage(session, message[i].getInputStream());
			    // logger.info("Content of Email:" +
			    // message[i].getContent());
			    String bodyOfEmail = null;
			    if (message[i].getContent() instanceof String) {
				bodyOfEmail = (String) message[i].getContent();
			    } else {
				bodyOfEmail = handleMultipartForGCSpecial((Multipart) message[i].getContent());
				Multipart parts = (Multipart) message[i].getContent();
				for (int count = 0; count < parts.getCount(); ++count) {
				    MimeBodyPart part = (MimeBodyPart) parts.getBodyPart(count);
				    if (Part.ATTACHMENT.equalsIgnoreCase(part.getDisposition()))
					++countAttachmentsGC;
				}
			    }
			    // logger.info("bodyOfEmail:" + bodyOfEmail);
			    mimeMessage.setContent(bodyOfEmail, "text/html");
			    // finalNameFile =
			    // extractFileNameFromEmail(bodyOfEmail,
			    // "extractFilename");
			    // finalUploadText =
			    // extractFileNameFromEmail(bodyOfEmail,
			    // "extractNotes");
			    String bodyEmail = extractEmailBodyPlaintext(bodyOfEmail);
			    finalNameFile = extractDataFromEmail(bodyEmail, "extractFilename");
			    finalUploadText = extractDataFromEmail(bodyEmail, "extractNotes");
			    logger.info("finalNameFile:" + finalNameFile);
			    logger.info("finalUploadText:" + finalUploadText);
			    logger.info("countAttachmentsGC:" + countAttachmentsGC);
			    if ((finalNameFile.length() == 0 || finalNameFile.equals("") || finalNameFile == null
			    /*
			     * || finalUploadText.equals("") || finalUploadText
			     * == null
			     */ ) && countAttachmentsGC >= 1) {
				logger.info("Inside the error condition:");
				isErrorFlag = true;
				sendEmail("invalidfilenameformat");
			    }

			    if (countAttachmentsGC > 1) {
				isErrorFlag = true;
				sendEmail("countattachments");
			    }

			    if (!isErrorFlag) {
				for (Address address : message[i].getFrom()) {
				    mimeMessage.setFrom(address);
				}

				mimeMessage.setSubject(message[i].getSubject());
				mimeMessage.setRecipients(RecipientType.TO, message[i].getRecipients(RecipientType.TO));
				mimeMessage.setRecipients(RecipientType.CC, message[i].getRecipients(RecipientType.CC));
				mimeMessage.setRecipients(RecipientType.BCC,
					message[i].getRecipients(RecipientType.BCC));
				mimeMessage.setSentDate(message[i].getSentDate());
				mimeMessage.saveChanges();
				mimeMessage.writeTo(bufferedOpGc);
				// message[i].writeTo(bufferedOpGc);
				bufferedOpGc.close();
				out.flush();
				out.close();
				long endTime1 = System.currentTimeMillis();
				System.out.println("Time taken for reading and writing using File streams : "
					+ (endTime1 - startTime1) + " milli seconds");

				gcEmailAttachmentsListNamesOriginal.add(emailNameOriginal);
				gcEmailAttachmentsListNamesModified.add(fileNameTemp);
			    }
			}

			if (!isErrorFlag) {
			    if (content instanceof Multipart) {
				handleMultipart((Multipart) content);
			    } else {
				handlePart(message[i]);
			    }
			}

			if (is_General_Corres && !isErrorFlag) {
			    logger.info("gcEmailAttachmentsListNamesOriginal");
			    for (int k = 0; k < gcEmailAttachmentsListNamesOriginal.size(); k++) {
				logger.info(k + ". " + gcEmailAttachmentsListNamesOriginal.get(k));
			    }
			    for (int j = 0; j < gcEmailAttachmentsListNamesModified.size(); j++) {
				logger.info(j + ". " + gcEmailAttachmentsListNamesModified.get(j));
			    }
			    doSpecialSavingForGC();
			}

			if (is_Emails_To_Delete.equalsIgnoreCase("YES")) {
			    moveMessage(message[i], archive);
			}

			message[i].setFlag(Flags.Flag.DELETED, true);
			emailData.setNumber_attachments(String.valueOf(count_Attachments));
			emailData.setAttachment_name(file_Names);
			emailData.setModified_fileName(modified_FileName);
			emailData_List.add(emailData);
			resetFlags();
		    }
		    if (emailData_List != null && !emailData_List.isEmpty()) {
			exportToCSV();
		    }
		    // 6. Close folder and close store.
		    if (inbox != null)
			inbox.close(true);
		    if (archive != null)
			archive.close(true);
		    store.close();
		    logger.info("Closed the store for emailbox");
		}

	    } catch (MessagingException e) {
		e.printStackTrace(System.out);
		logger.error(e.getMessage());
		stop_Flag = true;
	    } catch (IOException e) {
		e.printStackTrace(System.out);
		logger.error(e.getMessage());
		stop_Flag = true;
	    } catch (Exception e) {
		e.printStackTrace(System.out);
		logger.error(e.getMessage());
		stop_Flag = true;
	    }
	    System.out.println("Email Processor Running at " + Calendar.getInstance().getTime());
	}
    }

    /*
     * Methods to get the bodsy of the email
     * 
     * @param p
     * 
     * @return String
     */
    public static String getText(Part p) throws MessagingException, IOException {

	logger.info("Entered method getText " + Calendar.getInstance().getTime());

	boolean textIsHtml = false;

	if (p.isMimeType("text/*")) {
	    String s = (String) p.getContent();
	    textIsHtml = p.isMimeType("text/html");
	    return s;
	}

	if (p.isMimeType("multipart/alternative")) {
	    // prefer html text over plain text
	    Multipart mp = (Multipart) p.getContent();
	    String text = null;
	    logger.info("MimeType:multipart/alternative");
	    for (int i = 0; i < mp.getCount(); i++) {
		Part bp = mp.getBodyPart(i);

		if (bp.isMimeType("text/plain")) {
		    if (text == null)
			text = getText(bp);
		    continue;
		} else if (bp.isMimeType("text/html")) {
		    String s = getText(bp);
		    if (s != null)
			return s;
		} else {
		    return getText(bp);
		}
	    }
	    return text;
	} else if (p.isMimeType("multipart/*")) {
	    Multipart mp = (Multipart) p.getContent();
	    logger.info("MimeType:multipart/*");
	    for (int i = 0; i < mp.getCount(); i++) {
		String s = getText(mp.getBodyPart(i));
		if (s != null)
		    return s;
	    }
	}
	logger.info("Exited method getText " + Calendar.getInstance().getTime());
	return null;
    }

    /*
     * Method called from the Email Processor service to stop execution of the
     * Email Processor
     * 
     * @param args
     * 
     * @return void
     */
    public static void stop(String[] args) {
	System.out.println("stop");
	stop_Flag = true;
    }

    /*
     * Method to export the information about the files processed to the CSV
     * 
     * @param none
     * 
     * @return void
     */
    private static void exportToCSV() {

	boolean is_FileThere = false;

	logger.info("Entered method exportToCSV");

	String csvFile = "NOALog_" + new SimpleDateFormat("yyyy-MM-dd").format(Calendar.getInstance().getTime())
		+ ".csv";
	FileWriter writer;
	try {
	    File file = new File(log_Path + csvFile);
	    is_FileThere = file.exists();
	    file.createNewFile();
	    writer = new FileWriter(file, true);
	    System.out.println("File Exists" + file.exists());
	    if (!is_FileThere) {
		CSVUtils.writeLine(writer, Arrays.asList("Date", "Time", "Email Id", "Subject", "From", "Sent",
			"Received", "Received Time", "No of Attachments", "File Names", "Modified File Name"));
	    }
	    System.out.println("emailData_List" + emailData_List.size());
	    for (EmailData email : emailData_List) {

		List<String> list = new ArrayList<>();
		if (email.getPresent_date() != null) {
		    list.add(email.getPresent_date());
		} else {
		    list.add("");
		}
		if (email.getPresent_time() != null) {
		    list.add(email.getPresent_time());
		} else {
		    list.add("");
		}
		if (email.getEmail_Id() != null) {
		    list.add(email.getEmail_Id());
		} else {
		    list.add("");
		}
		if (email.getSubject() != null) {
		    list.add(email.getSubject());
		} else {
		    list.add("");
		}
		if (email.getFrom_email() != null) {
		    list.add(email.getFrom_email());
		} else {
		    list.add("");
		}
		if (email.getSent_date() != null) {
		    list.add(email.getSent_date());
		} else {
		    list.add("");
		}
		if (email.getReceived_date() != null) {
		    list.add(email.getReceived_date());
		} else {
		    list.add("");
		}
		if (email.getReceived_time() != null) {
		    list.add(email.getReceived_time());
		} else {
		    list.add("");
		}
		if (email.getNumber_attachments() != null) {
		    list.add(email.getNumber_attachments());
		} else {
		    list.add("");
		}
		if (email.getAttachment_name() != null) {
		    list.add(email.getAttachment_name());
		} else {
		    list.add("");
		}
		if (email.getModified_fileName() != null) {
		    list.add(email.getModified_fileName());
		} else {
		    list.add("");
		}
		System.out.println("email.getPresent_date()" + email.getPresent_date());
		System.out.println("email.getPresent_time()" + email.getPresent_time());
		System.out.println("email.getEmail_Id()" + email.getEmail_Id());
		System.out.println("email.getSubject()" + email.getSubject());
		System.out.println("email.getFrom_email()" + email.getFrom_email());
		System.out.println("email.getSent_date()" + email.getSent_date());
		System.out.println("email.getReceived_date()" + email.getReceived_date());
		System.out.println("email.getReceived_time()" + email.getReceived_time());
		System.out.println("email.getNumber_attachments()" + email.getNumber_attachments());
		System.out.println("email.getAttachment_name()" + email.getAttachment_name());
		System.out.println("email.getModified_fileName()" + email.getModified_fileName());
		CSVUtils.writeLine(writer, list);
	    }
	    writer.flush();
	    writer.close();
	} catch (IOException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace(System.out);
	    logger.error(e.getMessage());
	}

	logger.info("Exited method exportToCSV");
    }

    /*
     * Method to handle Multipart of emails.
     * 
     * @param multipart
     * 
     * @return void
     */
    public static void handleMultipart(Multipart multipart) throws MessagingException, IOException {

	logger.info("Entered method handleMultipart at " + Calendar.getInstance().getTime());

	for (int i = 0, n = multipart.getCount(); i < n; i++) {
	    handlePart(multipart.getBodyPart(i));
	}

	logger.info("Exited method handleMultipart at " + Calendar.getInstance().getTime());
    }

    /*
     * Method to handle Multipart of emails for GC.
     * 
     * @param multipart
     * 
     * @return void
     */
    public static String handleMultipartForGCSpecial(Multipart multipart) throws MessagingException, IOException {

	String bodyOfEmail = null;

	logger.info("Entered method handleMultipartForGCSpecial at " + Calendar.getInstance().getTime());

	for (int i = 0, n = multipart.getCount(); i < n; i++) {
	    bodyOfEmail = getText(multipart.getBodyPart(i));
	    if (bodyOfEmail != null) {
		// logger.info("bodyOfEmail in handleMultipartForGCSpecial" +
		// bodyOfEmail);
		break;
	    }
	}

	logger.info("Exited method handleMultipartForGCSpecial at " + Calendar.getInstance().getTime());

	return bodyOfEmail;
    }

    /*
     * Method to extract the Multipart type of emails.
     * 
     * @param part
     * 
     * @return void
     */
    public static void handlePart(Part part) throws MessagingException, IOException {

	logger.info("Entered method handlePart at" + Calendar.getInstance().getTime());

	String disposition = part.getDisposition();
	String contentType = part.getContentType();

	System.out.println("Disposition" + disposition);
	if (disposition == null) {
	    // When just body
	    System.out.println("contentType: " + contentType.toLowerCase().substring(0, 9));
	    // Check if plain
	    if ((contentType.length() >= 10) && ((contentType.toLowerCase().substring(0, 9).equals("text/html"))
		    || (contentType.toLowerCase().substring(0, 9).equals("text/plain")))) {
		if (is_ACC45) {
		    extractDateFromEmail((String) part.getContent());
		}
		logger.info("Inside the block of text/html");
		part.writeTo(System.out);
	    } else if (part.isMimeType("multipart/*")) {
		handleMultipart((Multipart) part.getContent());
	    } else { // Don't think this will happen
		System.out.println("Other body: " + contentType);
		part.writeTo(System.out);
	    }
	} else if (disposition.equalsIgnoreCase(Part.ATTACHMENT)) {
	    System.out.println("Attachment: " + part.getFileName() + " : " + contentType);
	    System.out.println("contentType" + contentType);
	    count_Attachments++;
	    if (count_Attachments > 1) {
		file_Names = file_Names + ":" + part.getFileName();
	    } else {
		file_Names = part.getFileName();
	    }
	    System.out.println("contentType:1" + contentType);
	    System.out.println(contentType.contains("application/octet-stream;"));
	    // if (!contentType.contains("application/pdf") &&
	    // !contentType.contains("application/octet-stream;")) {
	    // return;
	    // }
	    String fileExtension = getExtension(part.getFileName());
	    logger.info("FileExt: " + fileExtension);

	    if (!finalNameFile.endsWith(fileExtension)) {
		finalNameFile = finalNameFile + "." + fileExtension;
	    }
	    // else {
	    // finalNameFile = finalNameFile.substring(0,
	    // finalNameFile.lastIndexOf(".")) + fileExtension;
	    // }
	    saveFile(part.getFileName(), part.getInputStream());
	} else if (disposition.equalsIgnoreCase(Part.INLINE)) {
	    System.out.println("Inline: " + part.getFileName() + " : " + contentType);
	    // if (!contentType.contains("application/pdf") &&
	    // !contentType.contains("application/octet-stream;")) {
	    // return;
	    // }
	    saveFile(part.getFileName(), part.getInputStream());
	} else { // Should never happen
	    System.out.println("Other: " + disposition);
	}

	logger.info("Exited method handlePart at" + Calendar.getInstance().getTime());
    }

    private static String getExtension(String fileName) {
	char ch;
	int len;
	if (fileName == null || (len = fileName.length()) == 0 || (ch = fileName.charAt(len - 1)) == '/' || ch == '\\'
		|| // in the case of a directory
		ch == '.') // in the case of . or ..
	    return "";
	int dotInd = fileName.lastIndexOf('.'),
		sepInd = Math.max(fileName.lastIndexOf('/'), fileName.lastIndexOf('\\'));
	if (dotInd <= sepInd)
	    return "";
	else
	    return fileName.substring(dotInd + 1).toLowerCase();
    }

    /*
     * Method to extract date from email's subject line if it's of type ACC45
     * 
     * @param content
     * 
     * @return void
     */
    private static void extractDateFromEmail(String content) {

	String patternString = "we received a claim";
	Pattern pattern = null;
	Matcher matcher = null;

	logger.info("Entered method extractDateFromEmail at " + Calendar.getInstance().getTime());

	pattern = Pattern.compile(patternString);
	matcher = pattern.matcher(content);
	if (matcher.find()) {
	    acc45_Date = content.substring(matcher.start() - 11, matcher.start() - 1);
	}

	logger.info("Exited method extractDateFromEmail at " + Calendar.getInstance().getTime());
    }

    /*
     * Method to extract filename from email's body
     * 
     * @param content
     * 
     * @return void
     */
    private static String extractFileNameFromEmail(String content, String context) {

	String patternString = null;
	Pattern pattern = null;
	Matcher matcher = null;
	String value = null;

	logger.info("Entered method extractFileNameFromEmail at " + Calendar.getInstance().getTime());

	logger.info("content.indexOf('~')" + content.indexOf("~"));
	logger.info("content.lastIndexOf('~')" + content.lastIndexOf("~"));
	if (content.indexOf("~") == -1) {
	    logger.info("Inside first Validation" + content.indexOf("~"));
	    return "";
	}

	if (content.indexOf("~") == content.lastIndexOf("~")) {
	    logger.info("Inside second Validation" + content.indexOf("~"));
	    return "";
	}

	if (context.equalsIgnoreCase("extractFilename")) {
	    patternString = "Document name:";
	}
	if (context.equalsIgnoreCase("extractNotes")) {
	    patternString = "Notes:";
	}
	pattern = Pattern.compile(patternString);
	matcher = pattern.matcher(content);
	if (matcher.find()) {

	    value = content.substring(matcher.end()).split("[~]+")[0];
	}
	// logger.info("Content :" + content);
	logger.info("Value :" + value);

	if (context.equalsIgnoreCase("extractFilename") && value != null && !value.toLowerCase().endsWith(".pdf")) {
	    logger.info("Setting value to empty");
	    // If the filename extension is not specified then trigger error
	    // scenario.
	    value = "";
	}
	logger.info("Exited method extractFileNameFromEmail at " + Calendar.getInstance().getTime());

	return value.trim();
    }

    private static String extractDataFromEmail(String body, String context) {
	String value = "";

	logger.info("Entered method extractDataFromEmail at " + Calendar.getInstance().getTime());

	String[] lines = body.split("\\r?\\n");
	for (String line : lines) {
	    logger.info("line: " + line);
	    if (line.length() > 0 && line.trim() != "" && line.toLowerCase().contains("document")
		    && line.toLowerCase().contains("name") && context.equalsIgnoreCase("extractFilename"))

	    {
		value = line.substring(line.indexOf(":") + 1, line.length()).trim();
		if (value.length() > 0 && value.trim() != "") {
		    logger.info("Value of filename :" + value.length() + "..");
		    value = value.replaceAll("[+#^:;,@!$%&*()?'’<>\\{\\}\\[\\]\\/\\|]", "");
		}
		break;
	    }
	    if ((line.contains("Notes") && context.equalsIgnoreCase("extractNotes"))
		    || line.contains("notes") && context.equalsIgnoreCase("extractNotes")) {
		value = line.substring(line.indexOf(":") + 1, line.length()).trim();
		break;
	    }
	}
	logger.info("Value :" + value);
	logger.info("Exited method extractDataFromEmail at " + Calendar.getInstance().getTime());
	return value;
    }

    private static String extractEmailBodyPlaintext(String emailBody) {
	org.jsoup.nodes.Document extractedBody = null;
	logger.info("Entered method extractEmailBodyPlaintext at " + Calendar.getInstance().getTime());
	extractedBody = Jsoup.parse(emailBody.toString());
	String text = new HtmlToPlainText().getPlainText(extractedBody);
	logger.info("Extracted Mail Body :-\n");
	logger.info(text);
	logger.info("Exited method extractEmailBodyPlaintext at " + Calendar.getInstance().getTime());
	return text;
    }

    /*
     * Method to save the Multipart extracted from the emails
     * 
     * @param filename
     * 
     * @param input
     * 
     * @return void
     */
    public static void saveFile(String filename, InputStream input) throws IOException {

	String temp_FileName = null;

	logger.info("Entered method saveFile at " + Calendar.getInstance().getTime());

	if (filename == null) {
	    filename = File.createTempFile("xx", ".out").getName();
	}

	// Do no overwrite existing file
	if (is_ACC45) {
	    if (acc45_Date != null) {
		temp_FileName = filename.replace(".pdf",
			new Random().nextInt(range) + "_" + acc45_Date.replace("/", "-") + ".pdf");
		filename = "\\" + acc45_Hotfolder + temp_FileName;
	    } else {
		temp_FileName = filename.replaceAll(".pdf", new Random().nextInt(range) + ".pdf");
		filename = "\\" + acc45_Hotfolder + temp_FileName;
	    }
	} else if (is_Invoices) {
	    filename = filename.replaceAll("[+#^:;,@!$%&*()?'<>\\s\\{\\}\\[\\]\\/\\|]", "");
	    temp_FileName = filename.replaceAll(".pdf", new Random().nextInt(range) + ".pdf");
	    filename = "\\" + invoices_Hotfolder + temp_FileName;
	} else if (is_ACC18) {
	    temp_FileName = acc18_Hotfolder + filename.replaceAll(".pdf", new Random().nextInt(range) + ".pdf");
	    filename = "\\" + temp_FileName;
	} else if (is_General_Corres) {
	    // As per the new requirement there will be only one attachment per
	    // email for the GC. In that case we will have
	    // assign the filename extracted from the body of the email as the
	    // original file name. The actual name of the
	    // attachment has to be discarded and the name from the email body
	    // has to be used instead.
	    // gcEmailAttachmentsListNamesOriginal.add(filename);
	    gcEmailAttachmentsListNamesOriginal.add(finalNameFile);
	    temp_FileName = "\\" + email_Save_Directory + claimNumberFinal + "-" + (new Random().nextInt(90000) + 10000)
		    + categoryCodeFinal + ".out";
	    filename = temp_FileName;
	    gcEmailAttachmentsListNamesModified.add(filename);
	} else {
	    return;
	}
	valid_attachments++;
	if (valid_attachments > 1)
	    modified_FileName = modified_FileName + "-" + temp_FileName;
	else
	    modified_FileName = temp_FileName;

	File file = new File(filename);
	file.createNewFile();
	FileOutputStream fos = new FileOutputStream(file);
	BufferedOutputStream bos = new BufferedOutputStream(fos);
	BufferedInputStream bis = new BufferedInputStream(input);
	int aByte;
	while ((aByte = bis.read()) != -1) {
	    bos.write(aByte);
	}
	bos.flush();
	bos.close();
	bis.close();
	logger.info("Exited method saveFile at " + Calendar.getInstance().getTime());
    }

    /*
     * Method to do special saving for GC
     * 
     * @param null
     * 
     * @return void
     */
    private static void doSpecialSavingForGC() {

	String concatenatedName = "";
	String fileName = null;
	String topEmailFileName = null;

	logger.info("Entered method doSpecialSavingForGC at " + Calendar.getInstance().getTime());

	// Set files meta data with the original name of the file

	if (gcEmailAttachmentsListNamesOriginal != null && gcEmailAttachmentsListNamesOriginal.size() > 0) {
	    for (int i = 0; i < gcEmailAttachmentsListNamesOriginal.size(); i++) {
		if (i == 0) {
		    concatenatedName = gcEmailAttachmentsListNamesOriginal.get(i);
		} else {
		    // concatenatedName = concatenatedName + "," +
		    // gcEmailAttachmentsListNamesOriginal.get(i) + "-" + i;
		    concatenatedName = concatenatedName + "," + gcEmailAttachmentsListNamesOriginal.get(i);
		}
	    }
	    logger.info("concatenatedName " + concatenatedName);
	}

	if (gcEmailAttachmentsListNamesModified != null && gcEmailAttachmentsListNamesModified.size() > 0) {
	    for (int i = 0; i < gcEmailAttachmentsListNamesModified.size(); i++) {
		try {
		    File file = new File(gcEmailAttachmentsListNamesModified.get(i));
		    UserDefinedFileAttributeView view = Files.getFileAttributeView(file.toPath(),
			    UserDefinedFileAttributeView.class);

		    // User.notes will contain the notes information along
		    // passed in the email body
		    view.write("user.notes", Charset.defaultCharset().encode(finalUploadText));
		    // User.links will contain list of the email along with the
		    // attachments (comma separated)
		    view.write("user.links", Charset.defaultCharset().encode(concatenatedName));
		    // User.filename will contain the original filename whatever
		    // was received
		    view.write("user.filename",
			    Charset.defaultCharset().encode(gcEmailAttachmentsListNamesOriginal.get(i).toString()));

		    // The following retrieval is only for printing to see if
		    // the values are present in the file metadata, it has no
		    // significance in the functionality.
		    int sizeNotes = view.size("user.notes");
		    ByteBuffer bufferNotes = ByteBuffer.allocateDirect(sizeNotes);
		    view.read("user.notes", bufferNotes);
		    bufferNotes.flip();

		    logger.info("user.notes " + Charset.defaultCharset().decode(bufferNotes).toString());

		    // The following retrieval is only for printing to see if
		    // the values are present in the file metadata, it has no
		    // significance in the functionality.
		    int sizeLinks = view.size("user.links");
		    ByteBuffer bufferLinks = ByteBuffer.allocateDirect(sizeLinks);
		    view.read("user.links", bufferLinks);
		    bufferLinks.flip();

		    logger.info("user.links " + Charset.defaultCharset().decode(bufferLinks).toString());

		    // The following retrieval is only for printing to see if
		    // the values are present in the file metadata, it has no
		    // significance in the functionality.
		    int sizeFileName = view.size("user.filename");
		    ByteBuffer bufferFileName = ByteBuffer.allocateDirect(sizeFileName);
		    view.read("user.filename", bufferFileName);
		    bufferFileName.flip();

		    logger.info("user.filename " + Charset.defaultCharset().decode(bufferFileName).toString());

		    // Copy the attributes of the file to the new file ending in
		    // eml
		    File fileOld = new File(gcEmailAttachmentsListNamesModified.get(i));
		    fileName = fileOld.getAbsolutePath().replace(".out", ".eml");
		    File fileNew = new File(fileName);
		    // if (fileOld.renameTo(fileNew)) {
		    // logger.info("File Renamed " + fileNew.getName());
		    // }

		    Files.copy(fileOld.toPath(), fileNew.toPath(), COPY_ATTRIBUTES);

		} catch (IOException e) {
		    e.printStackTrace(System.out);
		    logger.error(e.getMessage());
		}
	    }

	}
	// Rename the file to .eml

	logger.info("Exited method doSpecialSavingForGC at " + Calendar.getInstance().getTime());
    }

    public static String extractFileName(String fileName) {
	if (fileName.lastIndexOf("\\") != -1 && fileName.lastIndexOf("\\") != 0)
	    return fileName.substring(fileName.lastIndexOf("\\") + 1);
	else
	    return "";

    }

    /*
     * Method to initialize the logger
     * 
     * @param none
     * 
     * @return none
     */
    public static void initializeLogger() {
	boolean append = true;
	Handler handler = null;
	try {
	    logger = Logger.getLogger(EmailProcessor.class.getName());
	} catch (SecurityException e) {
	    e.printStackTrace(System.out);
	    logger.error(e.getMessage());
	}
    }

    /*
     * Method to initialize the properties object
     * 
     * @param none
     * 
     * @return void
     */
    public static void initializeProperties() {

	logger.info("Loading properties file...");
	logger.info("Entered initializeProperties method at " + Calendar.getInstance().getTime());

	FileInputStream fileInputStream;
	try {
	    fileInputStream = new FileInputStream("configuration.properties");
	    props = new Properties();
	    props.load(fileInputStream);
	    // props.put("mail.imaps.socketFactory.class",
	    // "javax.net.ssl.SSLSocketFactory");
	    // props.put("mail.imaps.socketFactory.fallback", "false");
	    // props.put("mail.imaps.socketFactory.port",
	    // props.getProperty("EMAIL-IMAP-HOST-PORT"));
	    props.setProperty("mail.store.protocol", "imap");
	    props.setProperty("mail.imap.user", props.getProperty("EMAIL-IMAP-USERNAME"));
	    props.setProperty("mail.imap.host", props.getProperty("EMAIL-IMAP-HOSTNAME"));
	    props.setProperty("mail.imap.port", props.getProperty("EMAIL-IMAP-HOST-PORT"));
	    props.setProperty("mail.imap.partialfetch", "false");
	    props.setProperty("mail.imaps.partialfetch", "false");
	    // TRY
	    // props.setProperty("mail.debug", "true");
	    props.setProperty("mail.smtp.ssl.enable", "true");
	    // In future remove all socket factories and enable SSL

	    user_Name = props.getProperty("EMAIL-IMAP-USERNAME");
	    password = props.getProperty("EMAIL-IMAP-PASSWORD");
	    host_Name = props.getProperty("EMAIL-IMAP-HOSTNAME");
	    acc45_Hotfolder = props.getProperty("EMAIL-SAVE-ACC45-DIRECTORY");
	    invoices_Hotfolder = props.getProperty("EMAIL-SAVE-INVOICE-DIRECTORY");
	    acc18_Hotfolder = props.getProperty("EMAIL-SAVE-ACC18-DIRECTORY");
	    acc45_Sender_Address_Email = props.getProperty("EMAIL-ACC45-SENDER-ADDRESS-LIST");
	    acc18_Sender_Address_Email = props.getProperty("EMAIL-ACC18-SENDER-ADDRESS-LIST");
	    invoices_Sender_Address_Email = props.getProperty("EMAIL-INVOICE-SENDER-ADDRESS-LIST");
	    email_Save_Directory = props.getProperty("EMAIL-SAVE-DIRECTORY");
	    is_Emails_To_Delete = props.getProperty("EMAIL-IS-DELETE");
	    log_Path = props.getProperty("EMAIL-LOG-FILE-DIRECTORY");
	    folder_Read = props.getProperty("EMAIL-FOLDER-TO-READ");
	    folder_Archive = props.getProperty("EMAIL-FOLDER-TO-ARCHIVE");
	    general_Correspondence_Address_Email = props.getProperty("EMAIL-GC-SENDER-ADDRESS-LIST");
	    smtpHostName = props.getProperty("SMTP-HOST");
	    // smtpPortName = props.getProperty("SMTP-PORT");
	    // smtpEmailFrom = props.getProperty("SMTP-MAIL-FROM");
	    smtpEmailTo = props.getProperty("SMTP-EMAIL-TO");
	    // smtpSubject = props.getProperty("SMTP-EMAIL-SUBJECT");
	    general_Pattern_Address_Email = props.getProperty("GENERAL-NOA-EMAIL-DOMAIN");
	    smtpEmailInvalidEmailSubject = props.getProperty("SMTP-SUBJECT-INVALID-SUBJECT");
	    smtpEmailInvalidEmailClaim = props.getProperty("SMTP-SUBJECT-INVALID-CLAIM");
	    smtpEmailInvalidEmailCategory = props.getProperty("SMTP-SUBJECT-INVALID-CATEGORY");
	    smtpEmailInvalidEmailType = props.getProperty("SMTP-SUBJECT-INVALID-TYPE");

	    logger.info("Exited initializeProperties method at " + Calendar.getInstance().getTime());

	} catch (FileNotFoundException e) {
	    e.printStackTrace(System.out);
	    logger.error(e.getMessage());
	} catch (IOException e) {
	    e.printStackTrace(System.out);
	    logger.error(e.getMessage());
	}
    }

    /*
     * Method to check the email type ACC45, Invoice, ACC18 or GC
     * 
     * @param content
     * 
     * @param subject
     * 
     * @return void
     */
    public static void checkEmailFrom(String content, String subject) {

	String pattern_ACC45_Str = acc45_Sender_Address_Email;
	String pattern_Invoice_Str = invoices_Sender_Address_Email;
	String pattern_ACC18_Str = acc18_Sender_Address_Email;
	String pattern_General_Correspondence_Str = general_Correspondence_Address_Email;
	String pattern_General_NOA_Str = general_Pattern_Address_Email;
	String claimNumber = null;
	String category = null;
	String typeOfEamil = null;
	List extractList = new ArrayList<>();

	logger.info("Entered checkEmailFrom method at " + Calendar.getInstance().getTime());

	Pattern patternGeneral = Pattern.compile(pattern_General_NOA_Str);
	Matcher matcherGeneral = patternGeneral.matcher(content);

	if (matcherGeneral.matches()) {
	    Pattern patternACC45 = Pattern.compile(pattern_ACC45_Str);
	    Matcher matcherACC45 = patternACC45.matcher(content);
	    if (matcherACC45.find())
		is_ACC45 = true;

	    Pattern patternInvoices = Pattern.compile(pattern_Invoice_Str);
	    Matcher matcherInvoices = patternInvoices.matcher(content);
	    if (matcherInvoices.find())
		is_Invoices = true;

	    if (!is_ACC45 && !is_Invoices) {

		if (subject != null && !subject.equalsIgnoreCase("")) {
		    extractList = extractClaimNumberCategoryEmail(subject);
		}
		if (extractList.size() != 3) {
		    isErrorFlag = true;
		    errorMessage = smtpEmailInvalidEmailSubject;
		    sendEmail("subject_line");
		    return;
		}
		if (extractList.get(0) != null && extractList.get(0) != "") { // check
									      // claim
									      // number
									      // is
									      // valid
		    doJSONConnectionFigApp(extractList.get(0).toString().trim(), category, "search_using_claim_no");
		    /*
		     * if (isCheckACC45Number) {
		     * doJSONConnectionFigApp(extractList.get(0).toString().trim
		     * (), category, "search_using_acc45_no"); }
		     */
		    if (!isClaimNumberValid) {
			isErrorFlag = true;
			errorMessage = smtpEmailInvalidEmailClaim;
			sendEmail("claim_number");
			return;
		    }

		}
		if (extractList.get(1) != null && extractList.get(1) != "") {
		    String categoryCode = extractList.get(1).toString().trim();
		    System.out.println("Category Code" + categoryCode);
		    if (!categoryList.contains(categoryCode)) {
			errorMessage = smtpEmailInvalidEmailCategory;
			sendEmail("category_code");
			isErrorFlag = true;
		    } else {
			categoryCodeFinal = categoryCode;
			// Use this category for uploading documents to Figapp.
		    }

		    // Check if it is a valid category
		}
		if (extractList.get(2) != null && extractList.get(2) != "") {
		    String emailType = extractList.get(2).toString().trim();
		    System.out.println("Type" + emailType);
		    if (emailType.equalsIgnoreCase("GC")) {
			is_General_Corres = true;
		    } else if (emailType.equalsIgnoreCase("MC")) {
			is_ACC18 = true;
		    } else {
			errorMessage = smtpEmailInvalidEmailType;
			sendEmail("email_type");
			isErrorFlag = true;
		    }
		    // Check if it is a valid type
		}
	    }
	} else {
	    // Not from a valid domain send back an email saying, its not valid
	}

	// Pattern patternACC18 = Pattern.compile(pattern_ACC18_Str);
	// Matcher matcherACC18 = patternACC18.matcher(content);
	// if (matcherACC18.find())
	// is_ACC18 = true;
	//
	// Pattern patternGeneral =
	// Pattern.compile(pattern_General_Correspondence_Str);
	// Matcher matcherGeneralCorres = patternGeneral.matcher(content);
	// if (matcherGeneralCorres.find()) {
	// is_General_Corres = true;
	// }

	logger.info("is_ACC45 " + is_ACC45 + " is_invoices " + is_Invoices + " is_ACC18 " + is_ACC18
		+ " is_General_Corres " + is_General_Corres);
	logger.info("Exited checkEmailFrom method at " + Calendar.getInstance().getTime());

    }

    /*
     * Method to reset the global variables
     * 
     * @param none
     * 
     * @return void
     */
    public static void resetFlags() {

	logger.info("Entered resetFlags method at " + Calendar.getInstance().getTime());

	is_ACC45 = false;
	is_Invoices = false;
	is_ACC18 = false;
	is_General_Corres = false;
	file_Names = "";
	acc45_Date = null;
	count_Attachments = 0;
	modified_FileName = "";
	valid_attachments = 0;
	isClaimNumberValid = false;
	isCheckACC45Number = false;
	claimNumberFinal = null;
	isErrorFlag = false;
	errorMessage = null;
	subjectEmail = null;
	categoryCodeFinal = null;
	fileNameTemp = null;
	emailFrom = null;
	gcEmailAttachmentsListNamesOriginal.clear();
	gcEmailAttachmentsListNamesModified.clear();
	finalNameFile = "";
	finalUploadText = "";
	countAttachmentsGC = 0;
	logger.info("Exited resetFlags method at " + Calendar.getInstance().getTime());

    }

    /*
     * Method to move the message from Inbox to other folder
     * 
     * @param m
     * 
     * @param to
     * 
     * @return void
     */
    public static void moveMessage(Message m, Folder to) throws MessagingException {

	logger.info("Entered moveMessage method at " + Calendar.getInstance().getTime());

	m.getFolder().copyMessages(new Message[] { m }, to);

	logger.info("Entered moveMessage method at " + Calendar.getInstance().getTime());
    }

    /*
     * Method to send an email in case a business or runtime exection is
     * encountered
     * 
     * @param context
     * 
     * @return void
     */
    private static void sendEmail(String context) {

	HtmlEmailSender mailer = new HtmlEmailSender();
	String subject = null;
	String message = null;

	logger.info("Entered sendEmail method at " + Calendar.getInstance().getTime());

	try {

	    subject = errorMessage;
	    smtpEmailFrom = "Sender Name" + "<" + "no-reply@figtree.com" + ">";

	    if (context.equalsIgnoreCase("claim_number")) {
		message = "<h3><p>The claim number <font style=+ 'color:red'>"
			+ "in the following subject line </font> is invalid.</p></h3><br>" + subjectEmail;
	    }
	    if (context.equalsIgnoreCase("subject_line")) {
		if (subjectEmail != null && !subjectEmail.equalsIgnoreCase("")) {
		    message = "<h3><p>The subject line below <font style=+ 'color:red'>"
			    + "</font> is invalid. Please check the format.</p></h3><br>" + subjectEmail;
		} else {
		    message = "<h3><p>The subject line <font style=+ 'color:red'>" + "</font> is missing.</p></h3><br>";
		}
	    }
	    if (context.equalsIgnoreCase("category_code")) {
		message = "<h3><p>The subject line below<font style=+ 'color:red'>"
			+ "</font> has invalid category code.</p></h3><br>" + subjectEmail;
	    }
	    if (context.equalsIgnoreCase("email_type")) {
		message = "<h3><p>The subject line below <font style=+ 'color:red'>"
			+ "</font> has invalid email type.</p></h3><br>" + subjectEmail;
	    }
	    if (context.equalsIgnoreCase("invalidfilenameformat")) {
		message = "<h3><p>The Document Name or Notes format for the email with the following subject <font style=+ 'color:red'>"
			+ "</font> is incorrect. Please specify the correct format as follows"
			+ "<br>Document Name:xxxx.pdf" + "<br>Notes:xxx</p></h3><br>" + subjectEmail;
	    }
	    if (context.equalsIgnoreCase("countattachments")) {
		message = "<h3><p>This email with the following subject has more than  <font style=+ 'color:red'>"
			+ "</font>one attachment and cannot be processed.</p></h3><br>" + subjectEmail;
	    }
	    message = message + "<br><br><h4>NTT Data Figtree Support</h4>";
	    message = message
		    + "<h4>*** This is an automatically generated email, please do not reply to this message ***</h4>";
	    mailer.sendHtmlEmail(smtpHostName, "", smtpEmailFrom, "", emailFrom, subject, message, smtpEmailTo);
	    System.out.println("Email sent to : " + emailFrom + " and " + smtpEmailTo);
	} catch (Exception ex) {
	    System.out.println("Failed to sent email.");
	    ex.printStackTrace(System.out);
	}

	logger.info("Exited sendEmail method at " + Calendar.getInstance().getTime());
    }

    /*
     * Method to send request XML to FigApp
     * 
     * @param claimNumber
     * 
     * @param category
     * 
     * @param contextSearch
     * 
     * @return void
     */
    public static void doJSONConnectionFigApp(String claimNumber, String category, String contextSearch) {
	SimpleDateFormat sdf = new SimpleDateFormat("hh:mm:ss");
	Client client = null;
	RequestMessage requestMsg = null;
	ResponseMessage responseMsg = null;
	Element requestElement = null;
	String errorMessage = "";

	logger.info("Entered getClaim method at " + Calendar.getInstance().getTime());

	clientConfigJSON = getJsonConfig("figtree_client_config.json");
	requestConfigJSON = getJsonConfig("figtree_request_config.json");

	try {
	    if (contextSearch.equalsIgnoreCase("upload_GE")) {
		requestConfigJSON.put("function", "55");
		requestConfigJSON.put("time_requested", sdf.format(new Date()));
		requestConfigJSON.put("module", "GE");
		requestConfigJSON.put("COB", "9TL");
		requestConfigJSON.put("time_requested", sdf.format(new Date()));
	    } else if (contextSearch.equalsIgnoreCase("search_using_claim_no")) {
		requestConfigJSON.put("function", "003");
		requestConfigJSON.put("time_requested", sdf.format(new Date()));
		requestConfigJSON.put("module", "WC");
		requestConfigJSON.put("time_requested", sdf.format(new Date()));
	    } else if (contextSearch.equalsIgnoreCase("search_using_acc45_no")) {
		requestConfigJSON.put("function", "003");
		requestConfigJSON.put("time_requested", sdf.format(new Date()));
		requestConfigJSON.put("module", "WC");
		requestConfigJSON.put("time_requested", sdf.format(new Date()));
	    }
	    clientConfigJSON.put("type", ClientFactory.TYPE_SONICMQ);
	    client = ClientFactory.create(clientConfigJSON);
	    requestMsg = new RequestMessage(requestConfigJSON);

	    // Create the XML
	    requestElement = createXML(claimNumber, category, contextSearch);
	    requestMsg.setRequest(requestElement);
	    Document doc = requestMsg.getMessage();
	    System.out.println("Request:" + doc.asXML());
	    responseMsg = client.sendReceive(requestMsg);

	    Document rsDoc = responseMsg.getMessage();
	    System.out.println("Response:" + rsDoc.asXML());
	    List errorList = rsDoc.selectNodes("//Figtree_Systems/errors/error");
	    if (errorList.size() == 0) {
		if (contextSearch.equalsIgnoreCase("search_using_claim_no")
			|| contextSearch.equalsIgnoreCase("search_using_acc45_no")) {
		    List claimList = rsDoc.selectNodes("//Figtree_Systems/response/claims/claim");
		    for (int i = 0; i < claimList.size(); i++) {
			Element claimElm = (Element) claimList.get(i);
			if (claimElm.attributeValue("incident_number") != null
				&& !claimElm.attributeValue("incident_number").equalsIgnoreCase("")) {
			    claimNumberFinal = claimElm.attributeValue("incident_number");
			    isClaimNumberValid = true;
			    System.out.println("claimNumberFinal " + claimNumberFinal + "isClaimNumberValid "
				    + isClaimNumberValid);
			} else if (claimElm.attributeValue("incident_number") == null
				|| claimElm.attributeValue("incident_number").equalsIgnoreCase("")) {
			    isClaimNumberValid = false;
			}
		    }
		}
	    } else {
		for (int i = 0; i < errorList.size(); i++) {
		    Element errorElm = (Element) errorList.get(i);
		    errorMessage += errorElm.attributeValue("message") + " ";
		    System.out.println("Error Message" + errorMessage);
		    /*
		     * if (errorMessage != null && claimNumber != null &&
		     * errorMessage.contains(claimNumber)) { isCheckACC45Number
		     * = true; }
		     */ }
	    }

	} catch (JSONException e) {
	    logger.error(e.getMessage());
	    e.printStackTrace(System.out);
	} catch (FigAppException e) {
	    logger.error(e.getMessage());
	    e.printStackTrace(System.out);
	}

	logger.info("Exited getClaim method at " + Calendar.getInstance().getTime());
    }

    /*
     * Method to extract claim number from subject line for GC emails
     * 
     * @param subject
     * 
     * @return void
     */
    public static List<String> extractClaimNumberCategoryEmail(String subject) {

	List returnList = null;

	logger.info("Entered extractClaimNumberCategory method at " + Calendar.getInstance().getTime());

	returnList = new ArrayList<>();

	if (subject.toUpperCase().contains("FW:")) {
	    subject = subject.toUpperCase().replace("FW:", "");
	} else if (subject.toUpperCase().contains("RE:")) {
	    subject = subject.toUpperCase().replace("RE:", "");
	}

	if (subject != null && !subject.equalsIgnoreCase("")) {
	    String[] tempArrayHolderSplitComma = subject.split(",");
	    if (tempArrayHolderSplitComma.length == 3) {
		returnList.add(tempArrayHolderSplitComma[0].toString());
		returnList.add(tempArrayHolderSplitComma[1].toString());
		returnList.add(tempArrayHolderSplitComma[2].toString());
	    }
	}

	logger.info("Exited extractClaimNumberCategory method at " + Calendar.getInstance().getTime());

	return returnList;
    }

    /*
     * Method to create the XML for request to FigApp
     * 
     * @param claimNumber
     * 
     * @param category
     * 
     * @param contextSearch
     * 
     * @return Element
     */
    private static Element createXML(String claimNumber, String category, String contextSearch) {

	logger.info("Entered createXML method at " + Calendar.getInstance().getTime());
	Element request = DocumentHelper.createElement("request");

	if (contextSearch.equalsIgnoreCase("upload_GE")) {
	    request.addElement("mode").addAttribute("type", "add");
	    Element recordChild = request.addElement("record").addAttribute("key_number", claimNumber);
	    recordChild.addElement("field").addAttribute("name", "").addAttribute("table", "").addAttribute("value",
		    "");
	    Element confirmChild = request.addElement("confirm");
	    confirmChild.addElement("format").addAttribute("structure", "");
	    confirmChild.addElement("field").addAttribute("name", "").addAttribute("table", "");
	} else if (contextSearch.equalsIgnoreCase("search_using_claim_no")) {
	    request.addElement("criteria").addAttribute("incident_number", claimNumber);
	    Element fieldList = request.addElement("field_list");
	    fieldList.addElement("field").addAttribute("table", "").addText("incident_number");
	} else if (contextSearch.equalsIgnoreCase("search_using_acc45_no")) {
	    request.addElement("criteria").addText("claim.witness eq '" + claimNumber + "'");
	    Element fieldList = request.addElement("field_list");
	    fieldList.addElement("field").addAttribute("table", "").addText("incident_number");
	}

	logger.info("Exited createXML method at " + Calendar.getInstance().getTime());

	return request;

    }

    /*
     * Method to get the JSON connection object
     * 
     * @param storageConfigFile
     * 
     * @return JSONObject
     */
    public static JSONObject getJsonConfig(String storageConfigFile) {

	JSONObject jsonObject = null;

	logger.info("Entered getJsonConfig method at " + Calendar.getInstance().getTime());

	try {
	    File f = new File(storageConfigFile);
	    if (f.exists()) {
		InputStream is = new FileInputStream(storageConfigFile);
		String jsonTxt = IOUtils.toString(is);
		System.out.println(jsonTxt);
		jsonObject = new JSONObject(jsonTxt);
	    }
	} catch (Exception e) {
	    e.printStackTrace(System.out);
	    logger.error(e.getMessage());
	}

	logger.info("Exited getJsonConfig method at " + Calendar.getInstance().getTime());

	return jsonObject;

    }

}
