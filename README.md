# E-Ex Mass Gallery Uploader

A Windows desktop application for preparing image galleries and uploading them to E-Hentai / ExHentai. It provides a batch queue, a single-gallery workflow, gallery metadata controls, cover previews, and optional tools for looking up or translating titles.

> **Before uploading:** Check the destination, title, category, language, image order, and publication settings for every gallery. The **Publish** option can make a gallery available on the site; leave it unchecked if you intend to save a draft and review it first.

## Contents

- [Requirements](#requirements)
- [Getting started](#getting-started)
- [Using the batch queue](#using-the-batch-queue)
- [Single-gallery workflow](#single-gallery-workflow)
- [Images, archives, and sorting](#images-archives-and-sorting)
- [Account and session setup](#account-and-session-setup)
- [Cover and title tools](#cover-and-title-tools)
- [Saved files and privacy](#saved-files-and-privacy)
- [Running the Python source](#running-the-python-source)
- [Troubleshooting](#troubleshooting)
- [Sharing and distribution](#sharing-and-distribution)

## Requirements

- Windows and an internet connection for account validation and online features.
- Access to the relevant E-Hentai / ExHentai account and uploader.
- The complete application folder, including the executable and **_internal** folder.
- For RAR/CBR or 7Z content, a compatible extraction tool as described below.

The packaged application includes its Python runtime. You do **not** need to install Python just to launch the executable. Optional features may have additional requirements.

## Getting started

1. Extract the **entire** distribution archive to a folder with enough free space. Keep the file and folder structure intact.
2. Open the extracted folder and double-click **E-Ex Mass Gallery Uploader.exe**.
3. Enter your account information or provide a compatible cookie file, then select **Validate Session**.
4. In **Batch Queue Uploader**, add one or more image folders or archives.
5. Review the queue, image counts, titles, category, language, sort order, and publication settings.
6. When you are ready, select **Start batch**. Watch the queue status and process console for progress or errors.

Keep the **_internal** folder next to the executable. The program also includes an icon and the Python source file. Extracting only the executable is not enough to run this packaged version.

## Using the batch queue

### Add galleries

- **+Folders** adds one selected folder to the queue.
- **+Root** selects a parent folder and adds its immediate subfolders to the queue.
- **+Archives** selects supported archive files.
- You can also drag folders or supported archives onto the **gallery queue**. If you drop an individual non-archive file, the app adds its containing folder.

Each queue row represents a gallery source. Select a row to review its cover, titles, and available metadata in the inspector. Make sure the displayed image count and source path are correct before you start.

### Choose settings and review rows

The batch toolbar includes controls for category, language, destination folder, sort order, **Publish**, and **Unlisted**. These provide defaults for new additions; select individual rows to review and edit their settings. Check the current values instead of assuming that changing a toolbar option has updated every existing row.

The queue provides controls to pause or resume selected items or the batch, remove items, and clear the queue. Status information and details are shown in the queue and process console. The app saves queue information to disk so that it can restore entries when restarted; source paths must still be accessible. Resume behavior also depends on the state of the gallery and the server, so review a resumed item before publishing.

### Starting a batch

1. Confirm your session and verify that each source contains the intended images.
2. Check titles, per-gallery settings, sorting, and whether each gallery should be published or kept as a draft.
3. Select **Start batch** and monitor the status and process console.
4. Review any errors and verify the resulting galleries on the destination site.

Uploads and publication are network operations. Service availability, account permissions, website changes, file limits, and the site's current rules can affect the result.

## Single-gallery workflow

Select **Single Gallery Creation** when you want to prepare one gallery using the individual form. Supply the requested source and metadata, review its settings, and verify the publish/draft choice before submitting. Use the process console and the destination site to check the outcome.

## Images, archives, and sorting

Supported image extensions are **JPG, JPEG, PNG, GIF, and WebP**. The app accepts **ZIP, CBZ, RAR, CBR, and 7Z** archives.

| Format | Extraction support |
| --- | --- |
| ZIP / CBZ | Handled with Python's built-in ZIP support. |
| RAR / CBR | Requires compatible RAR extraction support, such as 7-Zip or WinRAR. |
| 7Z | Requires 7-Zip. |

The app looks for supported extractors on the system path and in common Windows installation folders. Password-protected, damaged, or inaccessible archives may fail. Archive contents can be extracted to a temporary directory during scanning and processing; allow sufficient free disk space.

A folder's directly contained supported images take precedence when present. If there are no direct images, the app can inspect supported archives in that folder. **+Root** adds immediate subfolders as separate queue entries; it is not a substitute for checking how your collection is organized.

Sorting options include natural, alphabetical, and reverse-natural order. Natural ordering treats numbers in names as numbers, so 1, 2, 10 appear in that order. Alphabetical ordering may place 10 before 2. Confirm the chosen order before upload.

## Account and session setup

The top of the window provides fields for account cookies, a cookie-file path, the **Use ExHentai** option, and **Validate Session**. You can enter supported cookie values manually or point the app to a compatible Netscape-format cookies.txt export. **File > Load Cookie File** can load the selected file.

When no cookie path is entered, the app looks for cookies.txt beside the executable. If a folder is supplied instead of a file, the app checks it for recognized cookie-file names. Select the appropriate destination option and validate your session before attempting an upload.

Cookies, account hashes, and API keys can grant access to an account. Treat them like passwords. Do not post them in issues, screenshots, repositories, or archives shared with others. A valid-looking cookie may still be expired or lack the site's required permissions.

## Cover and title tools

The app includes cover preview and optional title assistance, including metadata lookup, translation or romanization options, OCR-based title extraction, and links or workflows for image search. Availability and accuracy vary by provider, configuration, installed components, and network access. Review proposed titles before applying them; lookup results and machine translations can be incorrect.

Some search or translation actions may send a title or image to the selected third-party service. Check the selected provider and its handling of submitted material before using it.

OCR can require a separately installed OCR engine or other components. The packaged executable does not install Python packages into itself or automatically launch a local LibreTranslate instance. For those setup tasks, use the Python source in a suitable Python environment, or start a compatible LibreTranslate server separately and connect to it.

## Saved files and privacy

The app stores user data beside the executable (or beside the Python source when run as a script):

| File | Purpose |
| --- | --- |
| eh_uploader_config.json | Application settings; may contain account details or service settings. |
| eh_uploader_queue.json | Saved queue entries, metadata, and resume information; may contain local paths. |
| eh_uploader_cache.json | Cached lookup and translation data. |
| cookies.txt | Optional saved or exported session cookies. |
| eh_app_icon.ico | Application icon; the app can attempt to create it if it is missing. |

The clean distribution starts without the first four files. They may be created as you use the app. Separate extracted copies maintain separate data, and a saved queue may refer to paths that only exist on the original computer.

**Before sharing a copy or publishing a repository**, inspect it for cookies.txt, configuration, queues, caches, logs, API keys, and other personal data. Remove personal data from the copy you intend to distribute. Do not assume that a folder remains clean after you have used it.

## Running the Python source

The distribution includes **ex_gallery_uploader_2r.py** for people who want to inspect or run the source. The packaged app was built with Python 3.14. Running the source separately requires Python, Tkinter, and its Python dependencies in that environment. The core third-party packages include customtkinter, requests, beautifulsoup4, and Pillow; tkinterdnd2 enables drag-and-drop. Optional OCR, translation, browser, and archive features can require additional packages or applications.

For example, after installing Python 3.14 and ensuring Tkinter is available:

~~~powershell
py -3.14 -m pip install customtkinter requests beautifulsoup4 Pillow tkinterdnd2
py -3.14 .\ex_gallery_uploader_2r.py
~~~

Run these commands from the folder containing the source. The example installs the core dependencies, not every optional feature. Package installation and updates are separate from the bundled executable.

## Troubleshooting

### The app does not start

- Make sure the full archive was extracted and that **_internal** is next to the executable.
- Check that the files are accessible and that there is sufficient disk space.
- If running the source, verify that you are using the intended Python environment and have installed the required packages there.

### Drag-and-drop does not work

- Drop onto the **gallery queue**, not an unrelated area of the window.
- Look for the queue's drop hint and check the process console for a drag-and-drop error.
- Use **+Folders** or **+Archives** as an alternative.
- For the source version, tkinterdnd2 must be installed in the Python environment used to launch it.

### A folder or archive shows no images

- Confirm the path still exists and contains supported image types.
- Check the folder and archive arrangement described above.
- For RAR/CBR or 7Z, check that an appropriate extractor is installed and can open the archive outside the app.
- Check for archive damage, encryption, access errors, or insufficient temporary disk space.

### Session validation or upload fails

- Recheck the account fields, cookie-file path, and destination selection; refresh expired cookies if necessary.
- Confirm the account can access the uploader in a browser and has any required site permissions.
- Review the process console and the destination site's response. The site's behavior and availability may change.
- Verify the actual gallery state before retrying, especially after an interrupted creation or publication.

### A lookup or OCR feature is unavailable

- Check your network connection and the selected provider.
- Verify any external program, model, package, API key, or service required by that option.
- Review returned titles manually; providers can change or stop responding.

## Sharing and distribution

This folder contains a Windows build and source code. Keep the executable and **_internal** directory together when creating a distributable archive. Remove saved sessions and personal data from the copy being shared, and respect the destination site's rules and the rights associated with the content you upload. No separate project license is supplied in this folder; obtain appropriate permission before redistributing code or bundled components.
