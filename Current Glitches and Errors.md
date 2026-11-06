# Known Issues and Workarounds

## Publishing Galleries

The **Publish** checkbox hasn’t worked for me in either **Single Gallery Creation** or **Batch Queue Uploader**, despite repeated testing. Leave it unchecked. Your uploads will appear as unpublished galleries on your **Manage Gallery** page. Review them there and publish each gallery manually when you’re ready.

## Batch Settings and Saved Separately

The **Saved Separately** section in the upper-right corner is easy to miss. Use it when different folders in your queue need different gallery settings.

- **Sync** applies the batch settings for **Category**, **Folder**, **Language**, and **Unlisted** to **all queued folders**. Use it when you want the same settings across the queue.
- **Saved Separately** lets you set those options for an individual folder. Select the folder in the queue, then edit its settings in the upper-right panel.

If you need a mix of shared and individual settings, **Sync first**, then make your changes under **Saved Separately** for each folder. Review those rows again if you run Sync afterward.

## Translation Problems

- **Bing** sometimes fails to return a translation.
- **Lingva** is unlikely to work reliably.
- **DeepL** needs frequent updates to keep working.
- **SudachiPy**, **MeCab**, and **Cutlet** don’t function reliably in my testing. I haven’t figured out why.

The latest Python source, `ex_gallery_uploader_2r.py`, is included in the package. If you know how to get any of these providers working reliably, fixes are welcome.

## OCR Problems

- **English or Japanese title lookup** can fail even when you know the gallery is listed on E-Hentai, ExHentai, or nhentai. **Fetch** may return no match, and **Search E/Ex** may also fail for galleries you know are on E-Hentai or ExHentai.
- **Manual OCR** is a fallback when there’s no usable E/Ex gallery title, but it can take a lot of cleanup. Check the recognized text against the cover before using it as the gallery title.
